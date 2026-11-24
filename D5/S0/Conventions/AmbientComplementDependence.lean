/- GID: D5/S0/Conventions/AmbientComplementDependence
   generality: G
   mirror-B: D5/B/S0/Conventions/AmbientComplementDependence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Make subtraction complement determine and depend on its ambient total. -/

module
prelude
public import OmegaInit.Data.Int
public import OmegaMath.Topology.SimplicialCoboundary

namespace D5.S0.Conventions.AmbientComplementDependence

open Omega

/-- A subtraction complement has no ambient-free value or operation: equality at any fixed
argument, and equality of the whole operations, are each equivalent to equality of their
explicitly supplied ambient totals. -/
public theorem absolute_complement_requires_ambient_total
    {A : Type u} (group : AddCommGroup A) (laws : group.Laws) (u v e : A) :
    And (Iff (Eq (group.sub u e) (group.sub v e)) (Eq u v))
      (Iff (Eq (group.sub u) (group.sub v)) (Eq u v)) :=
  have recover (h : Eq (group.sub u e) (group.sub v e)) : Eq u v :=
    (group.sub_add_cancel laws u e).symm.trans
      ((congrArg (fun value => group.add value e) h).trans (group.sub_add_cancel laws v e))
  And.intro
    (Iff.intro recover (congrArg fun total => group.sub total e))
    (Iff.intro (fun h => recover (congrArg (fun operation => operation e) h))
      (congrArg group.sub))

/- Integer totals witness that changing the ambient total changes both outputs and operations. -/
example :
    let group := AddCommGroup.ofOperations Int.zero Int.add Int.neg
    let one := Int.ofNat Nat.zero.succ
    let two := Int.ofNat Nat.zero.succ.succ
    And (Not (Eq (group.sub one group.zero) (group.sub two group.zero)))
      (Not (Eq (group.sub one) (group.sub two))) :=
  let group := AddCommGroup.ofOperations Int.zero Int.add Int.neg
  let one := Int.ofNat Nat.zero.succ
  let two := Int.ofNat Nat.zero.succ.succ
  have distinct : Not (Eq (group.sub one group.zero) (group.sub two group.zero)) :=
    fun h => Eq.subst (Nat.rec (motive := fun _ => Prop) True (fun _ _ => False))
      (Nat.succ.inj (congrArg Int.natAbs h)) True.intro
  And.intro distinct (fun h => distinct (congrArg (fun operation => operation group.zero) h))

end D5.S0.Conventions.AmbientComplementDependence
