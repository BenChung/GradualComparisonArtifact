
class A { m(x: A): A { return this } }
class I { n(x:I):I { return this } }
class T {
s(x: I): T { return this }
t(x: any): any { return this.s(x) }
}
new T().t(new A())