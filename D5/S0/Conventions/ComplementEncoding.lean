/- GID: D5/S0/Conventions/ComplementEncoding
   generality: G
   mirror-B: D5/B/S0/Conventions/ComplementEncoding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Subtraction complement is involutive and determines its total. -/

import Mathlib.Algebra.Group.Basic
import D5.S0.FiniteGeometry.Simplicial.Coboundary

namespace D5.S0.Conventions.ComplementEncoding

/- The ambient element `u` is the total relative to which `e` is complemented. -/
def complement {G : Type*} [AddCommGroup G] (u e : G) : G := u - e

/- The complement operation has the endpoint, involution, and uniqueness laws. -/
theorem complement_encoding {A : Type*}
    (group : Omega.AddCommGroup A) (laws : group.Laws) (total effect : A) :
    Omega.And (Omega.Eq (group.sub total group.zero) total)
      (Omega.And (Omega.Eq (group.sub total total) group.zero)
        (Omega.And (Omega.Eq (group.sub total (group.sub total effect)) effect)
          (∀ other, Omega.Eq (group.sub other) (group.sub total) → Omega.Eq other total))) :=
  have atZero (ambient : A) : Omega.Eq (group.sub ambient group.zero) ambient :=
    (group.add_zero laws (group.sub ambient group.zero)).symm.trans
      (group.sub_add_cancel laws ambient group.zero)
  have restoreTotal : Omega.Eq (group.add effect (group.sub total effect)) total :=
    (laws.add_comm effect (group.sub total effect)).trans
      (group.sub_add_cancel laws total effect)
  have involution : Omega.Eq (group.sub total (group.sub total effect)) effect :=
    (Omega.congrArg (fun ambient => group.sub ambient (group.sub total effect))
      restoreTotal.symm).trans (group.add_sub_cancel_right laws effect (group.sub total effect))
  Omega.And.intro (atZero total) (Omega.And.intro (group.sub_self laws total)
    (Omega.And.intro involution (fun other equal =>
      (atZero other).symm.trans
        ((Omega.congrArg (fun operation => operation group.zero) equal).trans (atZero total)))))

private theorem toOmegaEq {A : Sort*} {x y : A} (h : x = y) : Omega.Eq x y :=
  h ▸ Omega.rfl

private theorem toStdEq {A : Sort*} {x y : A} (h : Omega.Eq x y) : x = y :=
  Omega.Eq.rec rfl h

/-- The complement laws in the standard additive group interface. -/
theorem complement_encoding_std {G : Type*} [AddCommGroup G] (u e : G) :
    (fun x : G => u - x) 0 = u ∧
      (fun x : G => u - x) u = 0 ∧
        (fun x : G => u - x) ((fun x : G => u - x) e) = e ∧
          ∀ v : G, (fun x : G => v - x) = (fun x : G => u - x) → v = u :=
  let group := Omega.AddCommGroup.ofOperations (0 : G) (· + ·) Neg.neg
  have laws : group.Laws :=
    Omega.AddCommGroup.Laws.intro group
      (fun a b c => toOmegaEq (add_assoc a b c))
      (fun a b => toOmegaEq (add_comm a b))
      (fun a => toOmegaEq (zero_add a))
      (fun a => toOmegaEq (neg_add_cancel a))
  have sub_transport (a b : G) : group.sub a b = a - b := (sub_eq_add_neg a b).symm
  have atZero (a : G) : a - 0 = a :=
    (sub_transport a 0).symm.trans (toStdEq (complement_encoding group laws a e).left)
  have result := complement_encoding group laws u e
  ⟨atZero u, (sub_transport u u).symm.trans (toStdEq result.right.left),
    (sub_transport u (u - e)).symm.trans
      ((congrArg (group.sub u) (sub_transport u e).symm).trans
        (toStdEq result.right.right.left)),
    fun v h => (atZero v).symm.trans ((congrFun h 0).trans (atZero u))⟩

end D5.S0.Conventions.ComplementEncoding
