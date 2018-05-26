class C:
	def m(self, x:C) -> C:
		return x
class D:
	def n(self, x:D) -> D:
		return x
class E:
	def m(self, x:D) -> D:
		return x
class F:
	def m(self, x:E) -> E:
		return x   
	def n(self, x:Dyn) -> Dyn:
		return self.m(x)
F().n(C()).m(C())