
class C { m(x: C): C { return x } }
class D { n(x: D): D { return x } }
class E { m(x: D): D { return x } }
class F {
m(x: E): E { return x }
n(x: any): any { return this.m(x) }
}
new F().n(new C()).m(new C())