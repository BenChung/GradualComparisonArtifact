class C:
	def n(self, x:C) -> C:
		return self
class Q:
	def m(self, x:Q) -> Q:
		return self     
class A:
	def m(self, x:A) -> A:
		return self
class I:
	def m(self, x:Q) -> I:
		return self
class T:
	def s(self, x:I) -> T:
		return self
	def t(self, x:Dyn) -> Dyn:
		return self.s(x)
T().t(A())