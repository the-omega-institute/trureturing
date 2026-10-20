module
public import LeanInformationAuditRegTests.DependencyFixtures.Base

namespace DependencyFixture.Users

public def importOnly : Nat := 0
public def typeOnly : DependencyFixture.Token := (0 : Nat)
public theorem direct : True := DependencyFixture.seed
private theorem helper : True := DependencyFixture.seed
public theorem throughHelper : True := helper
public theorem generated (n : Nat) : True :=
  match n with
  | 0 => helper
  | _ + 1 => DependencyFixture.seed

end DependencyFixture.Users
