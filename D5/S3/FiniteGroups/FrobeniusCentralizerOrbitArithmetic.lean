/- GID: D5/S3/FiniteGroups/FrobeniusCentralizerOrbitArithmetic
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/FrobeniusCentralizerOrbitArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The centralizer of a derangement acts freely in a Frobenius action. -/

import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.SetTheory.Cardinal.Finite

/-!
The centralizer/derangement arithmetic bridge for a Frobenius action: an element
commuting with a derangement and fixing `x` also fixes `d • x`. The two-point
fixed condition then forces that element to be the identity. Trivial stabilizers
give the orbit-product equivalence and hence centralizer-order divisibility.
-/

namespace D5.S3.FiniteGroups.FrobeniusCentralizerOrbitArithmetic

variable {G X : Type*} [Group G] [MulAction G X]

/-- Every nonidentity element of a derangement's centralizer moves every point
when nonidentity group elements have at most one fixed point. -/
theorem centralizer_smul_ne_self_of_ne_one
    (hfixed : ∀ g : G, g ≠ 1 → ∀ x y : X,
      g • x = x → g • y = y → x = y)
    {d : G} (hd : ∀ x : X, d • x ≠ x)
    (c : Subgroup.centralizer ({d} : Set G)) (hc : c ≠ 1) (x : X) :
    c • x ≠ x := by
  intro hcx
  have hcG : (c : G) ≠ 1 := fun h => hc (Subtype.ext h)
  have hcomm : (c : G) * d = d * (c : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp c.property
  have hcxG : (c : G) • x = x := hcx
  have hcdx : (c : G) • (d • x) = d • x := by
    calc
      (c : G) • (d • x) = d • ((c : G) • x) := by
        rw [← mul_smul, hcomm, mul_smul]
      _ = d • x := by rw [hcxG]
  exact hd x (hfixed (c : G) hcG x (d • x) hcxG hcdx).symm

/-- The order of a derangement's centralizer divides the degree of a finite
Frobenius action, including an action on the empty type. -/
theorem card_centralizer_dvd_card [Finite G] [Finite X]
    (hfixed : ∀ g : G, g ≠ 1 → ∀ x y : X,
      g • x = x → g • y = y → x = y)
    {d : G} (hd : ∀ x : X, d • x ≠ x) :
    Nat.card (Subgroup.centralizer ({d} : Set G)) ∣ Nat.card X := by
  have hfree : ∀ x : X,
      MulAction.stabilizer (Subgroup.centralizer ({d} : Set G)) x = ⊥ := by
    intro x
    apply eq_bot_iff.mpr
    intro c hcx
    change c = 1
    by_contra hc
    exact centralizer_smul_ne_self_of_ne_one hfixed hd c hc x
      (MulAction.mem_stabilizer_iff.mp hcx)
  have hcard := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hfree)
  rw [Nat.card_prod] at hcard
  refine ⟨Nat.card (Quotient
    (MulAction.orbitRel (Subgroup.centralizer ({d} : Set G)) X)), ?_⟩
  exact hcard.trans (Nat.mul_comm _ _)

#print axioms centralizer_smul_ne_self_of_ne_one
#print axioms card_centralizer_dvd_card

end D5.S3.FiniteGroups.FrobeniusCentralizerOrbitArithmetic
