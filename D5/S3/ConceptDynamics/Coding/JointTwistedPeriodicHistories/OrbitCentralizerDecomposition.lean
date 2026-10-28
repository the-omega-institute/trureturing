/- GID: D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/OrbitCentralizerDecomposition
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/OrbitCentralizerDecomposition
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: The raw conjugacy seam is grouped by the conjugation orbit, with one centralizer multiplicity for each orbit element.
-/

/- Orbit--centralizer refinement of the joint twisted coefficient count. -/

import D5.S3.ConceptDynamics.Coding.JointTwistedPeriodicHistories.TwistedJointPeriodicHistories
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.ConjAct

open scoped BigOperators Classical

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.ConceptDynamics.Coding.TwistedJointPeriodicHistories

open D5.S3.ConceptDynamics.Coding.CountedGroupOverlap (GroupMat)

universe u
variable {H : Type u} [Group H] [Fintype H] {n : ℕ}

private theorem weighted_orbit_sum
    {G X A : Type*}
    [Group G] [Fintype G] [MulAction G X] [AddCommMonoid A]
    (x : X)
    [Fintype (MulAction.orbit G x)]
    [Fintype (MulAction.stabilizer G x)]
    (f : X → A) :
    (∑ g : G, f (g • x)) =
      ∑ y : MulAction.orbit G x,
        Fintype.card (MulAction.stabilizer G x) • f (y : X) := by
  classical
  let e := MulAction.orbitProdStabilizerEquivGroup G x
  have hfst (g : G) :
      ((e.symm g).1 : X) = g • x := rfl
  simpa only [hfst, Fintype.sum_prod_type,
    Finset.sum_const, Finset.card_univ] using
    e.symm.sum_comp
      (fun p : MulAction.orbit G x × MulAction.stabilizer G x =>
        f (p.1 : X))

private theorem weighted_inv_conj_sum
    {H : Type*} [Group H] [Fintype H]
    (c : H) (f : H → ℕ) :
    (∑ z : H, f (z⁻¹ * c * z)) =
      ∑ y : MulAction.orbit (ConjAct H) c,
        Fintype.card (Subgroup.centralizer ({c} : Set H)) *
          f (y : H) := by
  classical
  have hcard :
      Fintype.card (MulAction.stabilizer (ConjAct H) c) =
        Fintype.card (Subgroup.centralizer ({c} : Set H)) := by
    exact Fintype.card_congr
      (show MulAction.stabilizer (ConjAct H) c ≃
          Subgroup.centralizer ({c} : Set H) from
        (MulEquiv.subgroupCongr
          (ConjAct.stabilizer_eq_centralizer c)).toEquiv)
  calc
    (∑ z : H, f (z⁻¹ * c * z)) =
        ∑ z : ConjAct H, f (z • c) := by
      refine Fintype.sum_equiv
        ((Equiv.inv H).trans ConjAct.toConjAct.toEquiv)
        _ _ ?_
      intro z
      exact congrArg f (ConjAct.toConjAct_inv_smul z c).symm
    _ = _ := by
      simpa only [hcard, Nat.nsmul_eq_mul] using
        (weighted_orbit_sum (G := ConjAct H) c f)

/-- The joint coefficient count groups the raw conjugacy seam by orbit, with
one centralizer multiplicity for every orbit element. -/
theorem jointTwistedPeriod_card_orbit_centralizer
    (C : GroupMat H n n) (h g : H) (d a b : ℕ)
    (hd : 0 < d)
    (hab : Nat.Coprime a b) (hc : Commute h g)
    (hpow : h ^ b = g ^ a) :
    @Fintype.card (JointTwistedPeriod C h g d a b)
      (jointTwistedPeriodFintype C h g d a b hd hab hc hpow) =
      ∑ i : Fin n, ∑ y : MulAction.orbit (ConjAct H)
          (h ^ (a.gcdA b) * g ^ (a.gcdB b)),
        Fintype.card (Subgroup.centralizer
          ({h ^ (a.gcdA b) * g ^ (a.gcdB b)} : Set H)) *
          ((C^d) i i).coeff (y : H) := by
  rw [jointTwistedPeriod_card C h g d a b hd hab hc hpow]
  apply Fintype.sum_congr
  intro i
  exact weighted_inv_conj_sum
    (h ^ (a.gcdA b) * g ^ (a.gcdB b))
    (fun y : H => ((C^d) i i).coeff y)

end D5.S3.ConceptDynamics.Coding.TwistedJointPeriodicHistories
