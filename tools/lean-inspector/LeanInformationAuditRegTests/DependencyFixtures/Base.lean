module

namespace DependencyFixture

public theorem seed : True := True.intro
public abbrev Token : Type := Nat
public inductive Shape where
  | point : Shape
public def emptyValue : Sort 2 := Type
public axiom absentValue : True

end DependencyFixture
