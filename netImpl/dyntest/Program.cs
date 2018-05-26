using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using System.Reflection.Emit;
using System.Runtime.CompilerServices;
using System.Runtime.Remoting;
using System.Text;
using System.Threading.Tasks;

namespace Kafka
{
    public struct LocationInfo
    {
        string filename;
        int line, index, column;
        public LocationInfo(string filename, int line, int index, int column)
        {
            this.filename = filename;
            this.line = line;
            this.index = index;
            this.column = column;
        }
    }
    public class CastException : Exception {
        LocationInfo loc;
        public CastException(LocationInfo loc)
        {
            this.loc = loc;
        }
    }

    public class Runtime
    {
        private static AssemblyName classGenName;
        private static AssemblyBuilder ab;
        private static ModuleBuilder mb;
        private static Type runtimeType;
        private static MethodInfo dyWrapperf, tyWrapperf;

        private static Dictionary<string, Type> dyWrappers = new Dictionary<string, Type>();
        private static Dictionary<Tuple<string, string>, Type> tyWrappers = new Dictionary<Tuple<string, string>, Type>();

        static Runtime()
        {
            classGenName = new AssemblyName("CastAssembly");
            ab = AppDomain.CurrentDomain.DefineDynamicAssembly(classGenName, AssemblyBuilderAccess.RunAndSave);
            mb = ab.DefineDynamicModule("KafkaWrappers"); //, "KafkaWrapper.dll"
            runtimeType = typeof(Runtime);
            dyWrapperf = runtimeType.GetMethod("dyWrapper");
            tyWrapperf = runtimeType.GetMethod("tyWrapper");
        }

        public static T rtCast<T>(dynamic arg, LocationInfo loc)
        {
            if (arg is T)
            {
                return (T)arg;
            } else
            {
                throw new CastException(loc);
            }
        }

        public static dynamic dyWrapper<T>(LocationInfo sourcelocation, T src)
        {
            Type source = typeof(T);
            Type wrapper = null;
            if (dyWrappers.ContainsKey(source.Name))
            {
                wrapper = dyWrappers[source.Name];
            } else
            {
                wrapper = makeDyWrapper(source, sourcelocation);
                dyWrappers[source.Name] = wrapper;
            }
            
            // no correctness criteria.
            // emit crank.
            //ab.Save("KafkaWrapper.dll");
            return (dynamic)wrapper.GetConstructor(new Type[] { source, typeof(LocationInfo) }).Invoke(new object[] { src, sourcelocation });
        }

        private static Type makeDyWrapper(Type source, LocationInfo sourcelocation)
        {
            BindingFlags flags = BindingFlags.Instance | BindingFlags.Public | BindingFlags.DeclaredOnly;

            MakeMemberMaps(source, flags, sourcelocation, out Dictionary<string, PropertyInfo> srcPropMap, out Dictionary<string, MethodInfo> srcMethMap);
            TypeBuilder tb = mb.DefineType(source.Name + "toDynwrapper", TypeAttributes.Public);
            // no interface implementations

            var thatf = tb.DefineField("that", source, FieldAttributes.Private);
            var locf = tb.DefineField("loc", typeof(LocationInfo), FieldAttributes.Private);
            MakeConstructor(source, tb, thatf, locf);


            foreach (string k in srcMethMap.Keys)
            {
                MethodInfo srcInfo = srcMethMap[k];
                MakeMethodWrapper(tb, thatf, locf, k, srcInfo, new Type[] { typeof(object) }, typeof(object), null, sourcelocation);
            }
            Type wrapper = tb.CreateType();
            //if ((source.Name + "toDynwrapper").Equals("CtoDynwrappertoIEwrappertoDynwrapper"))
            //    ab.Save("KafkaWrapper.dll");
            return wrapper;
        }

        public static T tyWrapper<T>(LocationInfo sourcelocation, dynamic src)
        {
            Type source = src.GetType();
            Type target = typeof(T);
            Type wrapper = null;

            var key = Tuple.Create(source.Name, target.Name);
            if (tyWrappers.ContainsKey(key))
            {
                wrapper = tyWrappers[key];
            }
            else
            {
                wrapper = maketywrapper(sourcelocation, source, target);
                tyWrappers[key] = wrapper;
            }

            //ab.Save("KafkaWrapper.dll");
            return (T)wrapper.GetConstructor(new Type[] { source, typeof(LocationInfo) }).Invoke(new object[] { src, sourcelocation });
        }

        private static Type maketywrapper(LocationInfo sourcelocation, Type source, Type target)
        {
            BindingFlags flags = BindingFlags.Instance | BindingFlags.Public | BindingFlags.DeclaredOnly;

            SubtypeOf sts = (SubtypeOf)Attribute.GetCustomAttribute(target, typeof(SubtypeOf));
            Type[] explicitSts = null;
            if (sts != null)
            {
                explicitSts = sts.Subtypes;
            }
            else
            {
                explicitSts = Type.EmptyTypes;
            }

            Dictionary<string, PropertyInfo> srcPropMap, tgtPropMap;
            Dictionary<string, MethodInfo> srcMethMap, tgtMethMap;
            MakeMemberMaps(source, flags, sourcelocation, out srcPropMap, out srcMethMap);
            MakeMemberMaps(target, flags, sourcelocation, out tgtPropMap, out tgtMethMap);

            foreach (string k in tgtPropMap.Keys)
            {
                if (!srcPropMap.ContainsKey(k)) throw new CastException(sourcelocation);
                if (tgtPropMap[k].CanRead && !srcPropMap[k].CanRead) throw new CastException(sourcelocation);
                if (tgtPropMap[k].CanWrite && !srcPropMap[k].CanWrite) throw new CastException(sourcelocation);
            }

            foreach (string k in tgtMethMap.Keys)
            {
                if (!srcMethMap.ContainsKey(k)) throw new CastException(sourcelocation);
            }

            //all compatibility checks done
            //time to turn the emit crank
            TypeBuilder tb = mb.DefineType(source.Name + "to" + target.Name + "wrapper", TypeAttributes.Public);
            tb.AddInterfaceImplementation(target);
            var thatf = tb.DefineField("that", source, FieldAttributes.Private);
            var locf = tb.DefineField("loc", typeof(LocationInfo), FieldAttributes.Private);
            MakeConstructor(source, tb, thatf, locf);

            Dictionary<string, PropertyBuilder> properties = new Dictionary<string, PropertyBuilder>();
            Dictionary<string, MethodBuilder> methods = new Dictionary<string, MethodBuilder>();

            foreach (string k in srcMethMap.Keys)
            {
                MethodInfo srcInfo = srcMethMap[k];
                MethodBuilder generated;
                if (tgtMethMap.ContainsKey(k))
                {
                    MethodInfo tgtInfo = tgtMethMap[k];
                    generated = MakeMethodWrapper(tb, thatf, locf, k, srcInfo,
                                             tgtInfo.GetParameters().Select(param => param.ParameterType).ToArray(),
                                             tgtInfo.ReturnType, tgtInfo, sourcelocation);
                }
                else
                {
                    generated = MakeMethodWrapper(tb, thatf, locf, k, srcInfo,
                                             srcInfo.GetParameters().Select(param => param.ParameterType).ToArray(),
                                             srcInfo.ReturnType, null, sourcelocation);
                }
                methods.Add(k, generated);
            }

            foreach (Type mbSt in explicitSts)
            {
                MakeExplicitImplementation(tb, mbSt, flags, properties, methods);
                tb.AddInterfaceImplementation(mbSt);
            }

            Type wrapper = tb.CreateType();
            return wrapper;
        }

        private static void MakeExplicitImplementation(TypeBuilder tb, Type mbSt, BindingFlags bf, Dictionary<string, PropertyBuilder> props, Dictionary<string, MethodBuilder> methods)
        {
            //We can assume: 
            // * The arguments are actually always going to be subtypes
            // * The return type is going to be statically known to be a subtype
            // * The real function is also on the same class, of the same name
            // If any of these were violated, the original structural rule wouldn't have worked.
            // The properties we don't have to care about, their type is invariant.
            foreach (MethodInfo mi in mbSt.GetMethods(bf))
            {
                var mb = tb.DefineMethod(mi.Name, MethodAttributes.Private | MethodAttributes.HideBySig
                                                | MethodAttributes.Virtual | MethodAttributes.Final | MethodAttributes.NewSlot, 
                                                mi.ReturnType, mi.GetParameters().Select(a => a.ParameterType).ToArray());
                var ilg = mb.GetILGenerator();
                ilg.Emit(OpCodes.Ldarg_0);
                ilg.Emit(OpCodes.Ldarg_1); // always 1 argument.
                var target = methods[mi.Name]; // must exist
                ilg.Emit(OpCodes.Call, target); // this.m(a)
                ilg.Emit(OpCodes.Ret);
                tb.DefineMethodOverride(mb, mi);
            }
        }

        private static void MakeMemberMaps(Type source, BindingFlags flags, LocationInfo sourcelocation, out Dictionary<string, PropertyInfo> srcPropMap, out Dictionary<string, MethodInfo> srcMethMap)
        {
            PropertyInfo[] srcProps = source.GetProperties();
            MethodInfo[] srcMeths = source.GetMethods(flags);
            try
            {
                srcPropMap = srcProps.ToDictionary(val => val.Name, val => val);
                srcMethMap = srcMeths.ToDictionary(val => val.Name, val => val);
            } catch (ArgumentException e)
            {
                throw new CastException(sourcelocation);
            }
        }

        private static void MakeConstructor(Type source, TypeBuilder tb, FieldBuilder thatf, FieldBuilder locf)
        {
            var cb = tb.DefineConstructor(MethodAttributes.Public, CallingConventions.Standard, new Type[] { source, typeof(LocationInfo) });
            var cbIlGen = cb.GetILGenerator();
            cbIlGen.Emit(OpCodes.Ldarg_0);
            cbIlGen.Emit(OpCodes.Ldarg_1);
            cbIlGen.Emit(OpCodes.Stfld, thatf);
            cbIlGen.Emit(OpCodes.Ldarg_0);
            cbIlGen.Emit(OpCodes.Ldarg_2);
            cbIlGen.Emit(OpCodes.Stfld, locf);
            cbIlGen.Emit(OpCodes.Ret);
        }

        private static MethodBuilder MakeMethodWrapper(TypeBuilder tb, FieldBuilder thatf, FieldBuilder locf, string k, MethodInfo srcInfo, Type[] argTypes, Type retType, MethodInfo tgtInfo, LocationInfo info)
        {
            var methodType = argTypes[0];
            var mb = tb.DefineMethod(k, MethodAttributes.Public | MethodAttributes.Virtual, retType, argTypes);
            var mil = mb.GetILGenerator();
            mil.Emit(OpCodes.Ldarg_0);
            mil.Emit(OpCodes.Ldfld, thatf);
            mil.Emit(OpCodes.Ldarg_0);
            mil.Emit(OpCodes.Ldfld, locf);
            mil.Emit(OpCodes.Ldarg_1);
            WrapValue(argTypes[0], srcInfo.GetParameters()[0].ParameterType, mil, info);
            mil.Emit(OpCodes.Callvirt, srcInfo);
            mil.Emit(OpCodes.Ldarg_0);
            mil.Emit(OpCodes.Ldfld, locf);
            WrapValue(srcInfo.ReturnType, retType, mil, info);
            mil.Emit(OpCodes.Ret);
            string written = mil.ToString();
            if (tgtInfo != null)
            {
                tb.DefineMethodOverride(mb, tgtInfo);
            }
            return mb;
        }

        private static void WrapValue(Type srcType, Type tgtType, ILGenerator ilgen, LocationInfo sourceloc)
        {
            if (srcType.IsEquivalentTo(typeof(object)) && tgtType.IsInterface) // * -> C
            {
                ilgen.Emit(OpCodes.Call, tyWrapperf.MakeGenericMethod(tgtType));
            }
            else if (srcType.IsInterface && tgtType.IsEquivalentTo(typeof(object))) // C -> *
            {
                ilgen.Emit(OpCodes.Call, dyWrapperf.MakeGenericMethod(srcType));
            }
            else if (srcType.IsEquivalentTo(tgtType)) { /* do zip */ }
            else
            {
                throw new CastException(sourceloc);
            }
        }
    }
    [System.AttributeUsage(AttributeTargets.Interface, Inherited = false, AllowMultiple = false)]
    public sealed class SubtypeOf : Attribute
    {
        readonly Type[] of;

        public SubtypeOf(params Type[] of)
        {
            this.of = of;
        }

        public Type[] Subtypes
        {
            get { return of; }
        }
    }
    /*
    public interface IC { }

    public class D : IC { }

    [SubtypeOf(typeof(IB))]
    public interface IA
    {
        IC x(IC y);
    }
    [SubtypeOf(typeof(IA))]
    public interface IB
    {
        IC x(IC y);
    }
    public class A : IC
    {
        public object x(object y)
        {
            return new A();
        }
    }
    class Program
    {
        public static void Main(String[] args)
        {
            var ret = Runtime.tyWrapper<IA>(new A());
            new A().x(new A());
            var bed = (IB)ret;
            bed.x(new A());
        }
    }
    */
}
