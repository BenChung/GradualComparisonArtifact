
class Q { n(x: Q): Q { return this } }
class A { m(x: A): A { return this } }
class I { m(x:Q):I { return this } }
class T {
s(x: I): T { return this }
t(x: any): any { return this.s(x) }
}
new T().t(new A())