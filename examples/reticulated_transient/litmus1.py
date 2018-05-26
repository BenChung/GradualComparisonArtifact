class A:
	def m(self, x:A) -> A:
		return self
class I:
	def n(self, x:I) -> I:
		return self
class T:
	def s(self, x:I) -> T:
		return self
def t(self, x:Dyn) -> Dyn:
	return self.s(x)
T().t(A())