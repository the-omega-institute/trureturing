/- GID: D5/S0/Certificates/RootDeltaFineRings
   generality: G
   mirror-B: D5/B/S0/Certificates/RootDeltaFineRings
   mirror-E: none(waiver:arbitrary-ring-resolution)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.Units, mathlib/module/Mathlib.RingTheory.Nilpotent.Defs]
   utility: none
   digest: Every root-Delta-fine associative unital ring is fine, and its Delta is zero. -/



import Mathlib.Algebra.Ring.Units
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.RingTheory.Nilpotent.Defs

/-!
Danchev, Hasanzadeh, Moussavi and Javan, arXiv:2608.30734v2,
displayed Problem 4.4: "Is there a sqrt(Delta)-fine ring which is not fine?"
The answer is No under the explicit unit-test definitions, in every universe.
The surrounding source prose has conflicting conjectural polarities; no radical
characterization or commutation assumption is used here.

The live structural construction is `delta_eq_zero`: decomposition of a nonzero
Delta member makes its root-Delta summand a unit, a contradiction.
The auxiliary `zero_delta` and `delta_not_unit` are consumed by the structural
proof and converse. The implication and converse are consumed by the equivalence;
the no-existence endpoint is the displayed external question's resolution.
-/

set_option autoImplicit false

namespace D5.S0.Certificates.RootDeltaFineRings

universe u
variable {R : Type u} [Ring R]

/-- Source Introduction: the test is left multiplication by every two-sided unit. -/
def DeltaMember (d : R) : Prop :=
  ∀ v : Rˣ, IsUnit (1 - (v : R) * d)

/-- Source Introduction: the root exponent is positive. -/
def RootDeltaMember (a : R) : Prop :=
  ∃ n : ℕ, 0 < n ∧ DeltaMember (a ^ n)

/-- Source Definition 2.1: all nonzero elements, with no commuting condition. -/
def RootDeltaFine (R : Type u) [Ring R] : Prop :=
  ∀ r : R, r ≠ 0 → ∃ (v : Rˣ) (a : R),
    r = (v : R) + a ∧ RootDeltaMember a

/-- Source Introduction: every nonzero element is a unit plus a nilpotent. -/
def Fine (R : Type u) [Ring R] : Prop :=
  ∀ r : R, r ≠ 0 → ∃ (v : Rˣ) (a : R),
    r = (v : R) + a ∧ IsNilpotent a

theorem zero_delta : DeltaMember (0 : R) := by
  intro v
  simpa using (isUnit_one : IsUnit (1 : R))

theorem delta_not_unit [Nontrivial R] {d : R}
    (hd : DeltaMember d) (hu : IsUnit d) : False := by
  rcases hu with ⟨v, rfl⟩
  have h := hd v⁻¹
  have hz : IsUnit (0 : R) := by simpa using h
  exact not_isUnit_zero hz

/-- The sole nontrivial structural step applies the decomposition to Delta itself. -/
theorem delta_eq_zero (h : RootDeltaFine R) {d : R}
    (hd : DeltaMember d) : d = 0 := by
  by_contra hne
  letI : Nontrivial R := ⟨⟨d, 0, hne⟩⟩
  obtain ⟨v, a, hdec, n, hn, hpow⟩ := h d hne
  have hb : IsUnit (1 - ((v⁻¹ : Rˣ) : R) * d) := hd v⁻¹
  have hfactor : (-(v : R)) * (1 - ((v⁻¹ : Rˣ) : R) * d) = a := by
    rw [neg_mul, mul_sub, mul_one, ← mul_assoc, Units.mul_inv, one_mul,
      neg_sub, hdec, add_sub_cancel_left]
  have ha : IsUnit a := hfactor ▸ v.isUnit.neg.mul hb
  exact delta_not_unit hpow (ha.pow n)

theorem rootDeltaFine_implies_fine (h : RootDeltaFine R) : Fine R := by
  intro r hr
  obtain ⟨v, a, hdec, n, hn, hpow⟩ := h r hr
  exact ⟨v, a, hdec, n, delta_eq_zero h hpow⟩

theorem fine_implies_rootDeltaFine (h : Fine R) : RootDeltaFine R := by
  intro r hr
  obtain ⟨v, a, hdec, n, hn⟩ := h r hr
  refine ⟨v, a, hdec, n + 1, Nat.zero_lt_succ n, ?_⟩
  simpa [pow_succ, hn] using (zero_delta : DeltaMember (0 : R))

theorem rootDeltaFine_iff_fine : RootDeltaFine R ↔ Fine R :=
  ⟨rootDeltaFine_implies_fine, fine_implies_rootDeltaFine⟩

/-- Exact displayed Problem 4.4: no source-admissible counterexample exists. -/
theorem no_rootDeltaFine_not_fine : ¬ (RootDeltaFine R ∧ ¬ Fine R) := by
  rintro ⟨h, hn⟩
  exact hn (rootDeltaFine_implies_fine h)

#check rootDeltaFine_implies_fine
#check fine_implies_rootDeltaFine
#check no_rootDeltaFine_not_fine
#check delta_eq_zero
#check rootDeltaFine_iff_fine
#print axioms rootDeltaFine_iff_fine
#print axioms delta_eq_zero
#print axioms rootDeltaFine_implies_fine
#print axioms fine_implies_rootDeltaFine
#print axioms no_rootDeltaFine_not_fine

end D5.S0.Certificates.RootDeltaFineRings
