/- GID: D5/S3/Topology/Measures/AchievementResidueConverseRefutation
   generality: I
   mirror-B: D5/B/S3/Topology/Measures/AchievementResidueConverseRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Topology/Measures/AchievementResidueConverseRefutation.claim; result=D5/S3/Topology/Measures/AchievementResidueConverseRefutation.result; claim=D5/S3/Topology/Measures/AchievementResidueConverseRefutation.claim
   digest: Indexed multigeometric subsums and the unnormalized residue converse -/

import Mathlib.Analysis.Real.OfDigits
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-!
The coefficients are indexed: equal coefficients at distinct positions remain
independently selectable. The first block has denominator exponent one.
The source question is Problem 9 of arXiv:2512.17285v1, also Problem 1 in
Section 5.1 of arXiv:2508.19454v1. The normalized and primitive variants are
different assertions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set MeasureTheory
open scoped BigOperators

namespace D5.S3.Topology.Measures.AchievementResidueConverseRefutation

/-- Distinct values of independently selectable indexed Boolean block sums. -/
def blockSums {m : ℕ} (k : Fin m → ℕ) : Finset ℕ :=
  Finset.univ.image (fun b : Fin m → Bool => ∑ i, if b i then k i else 0)

/-- The zero-based form of the source sequence, with its exponent-one first block. -/
noncomputable def sourceTerm {m : ℕ} (hm : 0 < m) (k : Fin m → ℕ)
    (n t : ℕ) : ℝ :=
  (k ⟨t % m, Nat.mod_lt t hm⟩ : ℝ) / (n : ℝ) ^ (t / m + 1)

/-- Actual convergent subseries on arbitrary subsets of the original indices. -/
def achievement {m : ℕ} (hm : 0 < m) (k : Fin m → ℕ) (n : ℕ) : Set ℝ :=
  {x | ∃ A : Set ℕ, HasSum (fun t : A => sourceTerm hm k n t.val) x}

/-- The full unnormalized residue implication, with no free parameters. -/
def claim : Prop :=
  ∀ (m : ℕ) (hm : 0 < m) (k : Fin m → ℕ) (n : ℕ),
    (∀ i, 0 < k i) → Antitone k → 1 < n → (blockSums k).card = n →
    (∀ i, ¬ n ∣ k i) → 0 < volume (achievement hm k n) →
    (blockSums k).image (fun s => s % n) = Finset.range n

private def coefficients : Fin 3 → ℕ := ![9, 3, 3]

private def blockDigit (b : Fin 3 → Bool) : Fin 6 :=
  ⟨(if b 0 then 3 else 0) + (if b 1 then 1 else 0) +
    (if b 2 then 1 else 0), by split_ifs <;> omega⟩

private def digitBits (d : Fin 6) : Fin 3 → Bool :=
  ![decide (3 ≤ d.val), decide (1 ≤ d.val % 3), decide (d.val % 3 = 2)]

private lemma digitBits_right : ∀ d : Fin 6, blockDigit (digitBits d) = d := by
  decide

private lemma block_value (b : Fin 3 → Bool) :
    (∑ i, if b i then (coefficients i : ℝ) else 0) = 3 * (blockDigit b : ℝ) := by
  simp [Fin.sum_univ_succ, coefficients, blockDigit]
  split_ifs <;> norm_num

private noncomputable def weight (p : ℕ × Fin 3) : ℝ :=
  (coefficients p.2 : ℝ) / (6 : ℝ) ^ (p.1 + 1)

private lemma source_block (p : ℕ × Fin 3) :
    sourceTerm (by decide : 0 < 3) coefficients 6 ((Nat.divModEquiv 3).symm p) =
      weight p := by
  rcases p with ⟨j, i⟩
  simp only [Nat.divModEquiv_symm_apply, sourceTerm, weight]
  rw [Nat.mul_add_mod_of_lt i.isLt]
  congr 2
  omega

private lemma weight_nonneg (p : ℕ × Fin 3) : 0 ≤ weight p := by
  unfold weight
  positivity

private lemma weight_summable : Summable weight := by
  apply (summable_prod_of_nonneg weight_nonneg).2
  refine ⟨fun _ => summable_fintype _, ?_⟩
  have h := (Real.summable_ofDigitsTerm (digits := fun _ => (5 : Fin 6))).mul_left 3
  convert h using 1
  funext j
  simp [tsum_fintype, weight, coefficients, Fin.sum_univ_succ,
    Real.ofDigitsTerm, div_eq_mul_inv]
  ring

private lemma source_summable :
    Summable (sourceTerm (by decide : 0 < 3) coefficients 6) := by
  apply (Nat.divModEquiv 3).symm.summable_iff.mp
  simpa only [Function.comp_def, source_block] using weight_summable

private lemma selected_summable (A : Set ℕ) :
    Summable (fun t : A => sourceTerm (by decide : 0 < 3) coefficients 6 t.val) :=
  source_summable.subtype A

private noncomputable def selectedBits (A : Set ℕ) (j : ℕ) : Fin 3 → Bool :=
  fun i => decide ((Nat.divModEquiv 3).symm (j, i) ∈ A)

private noncomputable def selectedDigits (A : Set ℕ) : ℕ → Fin 6 :=
  fun j => blockDigit (selectedBits A j)

private lemma selected_row (A : Set ℕ) (j : ℕ) :
    (∑' i : Fin 3,
      A.indicator (sourceTerm (by decide : 0 < 3) coefficients 6)
        ((Nat.divModEquiv 3).symm (j, i))) =
      3 * Real.ofDigitsTerm (selectedDigits A) j := by
  classical
  simp only [tsum_fintype, source_block]
  have h := block_value (selectedBits A j)
  simp only [selectedBits, Bool.decide_coe] at h
  simp only [Set.indicator_apply, weight, Real.ofDigitsTerm, selectedDigits]
  rw [← mul_assoc, ← h]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all [div_eq_mul_inv]

private lemma selected_hasSum (A : Set ℕ) :
    HasSum (fun t : A => sourceTerm (by decide : 0 < 3) coefficients 6 t.val)
      (3 * Real.ofDigits (selectedDigits A)) := by
  classical
  have hs := source_summable.indicator A
  have hp : Summable (fun p : ℕ × Fin 3 =>
      A.indicator (sourceTerm (by decide : 0 < 3) coefficients 6)
        ((Nat.divModEquiv 3).symm p)) :=
    (Nat.divModEquiv 3).symm.summable_iff.mpr hs
  have he : (∑' t : A, sourceTerm (by decide : 0 < 3) coefficients 6 t.val) =
      3 * Real.ofDigits (selectedDigits A) := by
    rw [tsum_subtype]
    rw [← (Nat.divModEquiv 3).symm.tsum_eq
      (A.indicator (sourceTerm (by decide : 0 < 3) coefficients 6))]
    rw [hp.tsum_prod]
    simp_rw [selected_row]
    exact tsum_mul_left
  exact he ▸ (selected_summable A).hasSum

private noncomputable def digitSelection (d : ℕ → Fin 6) : Set ℕ :=
  {t | digitBits (d (t / 3)) ⟨t % 3, Nat.mod_lt t (by decide)⟩ = true}

private lemma digitSelection_digits (d : ℕ → Fin 6) :
    selectedDigits (digitSelection d) = d := by
  classical
  funext j
  unfold selectedDigits
  rw [← digitBits_right (d j)]
  congr 1
  funext i
  simp [selectedBits, digitSelection, Nat.divModEquiv_symm_apply,
    Nat.mul_add_mod_of_lt i.isLt, Nat.add_comm, Nat.add_mul_div_right,
    Nat.div_eq_of_lt i.isLt]

private lemma achievement_interval :
    achievement (by decide : 0 < 3) coefficients 6 = Icc 0 3 := by
  ext x
  constructor
  · rintro ⟨A, hA⟩
    have hx := hA.unique (selected_hasSum A)
    rw [hx]
    constructor
    · positivity
    · have := Real.ofDigits_le_one (selectedDigits A)
      linarith
  · intro hx
    have hz : x / 3 ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [hx.1, hx.2]
    obtain ⟨d, _, hd⟩ := Real.ofDigits_SurjOn (by decide : 1 < 6) hz
    refine ⟨digitSelection d, ?_⟩
    have h := selected_hasSum (digitSelection d)
    rw [digitSelection_digits, hd] at h
    convert h using 1 <;> ring

/-- The public result is the designated refutation result (`basis=refutes`)
and is exempt from four-slot escape registration. -/
theorem result : ¬ claim := by
  intro h
  have hc : (blockSums coefficients).card = 6 := by decide
  have hpos : ∀ i, 0 < coefficients i := by decide
  have hord : Antitone coefficients := by decide
  have hdiv : ∀ i, ¬ 6 ∣ coefficients i := by decide
  have hmeasure : 0 < volume (achievement (by decide : 0 < 3) coefficients 6) := by
    rw [achievement_interval, Real.volume_Icc]
    norm_num
  have he := h 3 (by decide) coefficients 6 hpos hord (by decide) hc hdiv hmeasure
  have hmissing : 1 ∉ (blockSums coefficients).image (fun s => s % 6) := by decide
  rw [he] at hmissing
  exact hmissing (by decide)

end D5.S3.Topology.Measures.AchievementResidueConverseRefutation
