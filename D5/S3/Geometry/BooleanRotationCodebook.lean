/- GID: D5/S3/Geometry/BooleanRotationCodebook
   generality: G
   mirror-B: D5/B/S3/Geometry/BooleanRotationCodebook
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Group.AddCircle]
   utility: none
   digest: Boolean subset queries determine the exact signed simplex difference below the no-wrap threshold. -/
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace D5.S3.Geometry.BooleanRotationCodebook

/-- Circular distance from zero, with the literal period retained. -/
def circularError (L t : ℝ) : ℝ := ‖(t : AddCircle L)‖

private lemma small_nonnegative_close {L ε t : ℝ} (hε : 0 ≤ ε)
    (hL : 3 * ε < L) (ht : 0 ≤ t) (ht' : t ≤ 2 * ε)
    (h : circularError L t ≤ ε) : t ≤ ε := by
  rw [circularError, AddCircle.norm_eq] at h
  let k : ℤ := round (L⁻¹ * t)
  have hab : |t - (k : ℝ) * L| ≤ ε := h
  obtain ⟨hlo, hhi⟩ := abs_le.mp hab
  have hLp : 0 < L := by linarith
  have hk0 : 0 ≤ k := by
    by_contra hn
    have hk : k ≤ -1 := by omega
    have hkr : (k : ℝ) ≤ -1 := by exact_mod_cast hk
    have := mul_le_mul_of_nonneg_right hkr hLp.le
    nlinarith
  have hk1 : k ≤ 0 := by
    by_contra hn
    have hk : 1 ≤ k := by omega
    have hkr : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have := mul_le_mul_of_nonneg_right hkr hLp.le
    nlinarith
  have hk : k = 0 := le_antisymm hk1 hk0
  simpa [hk] using hhi

/-- A finite first crossing cannot jump across the forbidden circular gap. -/
theorem nonnegative_sum_no_wrap {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) {L ε : ℝ} (hε : 0 ≤ ε) (hL : 3 * ε < L)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ ε)
    (hq : ∀ t ⊆ s, circularError L (∑ i ∈ t, a i) ≤ ε) :
    ∑ i ∈ s, a i ≤ ε := by
  induction s using Finset.induction_on with
  | empty => simpa using hε
  | @insert i s hi ih =>
    have hs : ∑ j ∈ s, a j ≤ ε := ih
      (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      (fun t ht => hq t (ht.trans (Finset.subset_insert i s)))
    have hai := ha i (Finset.mem_insert_self i s)
    have hnon : 0 ≤ ∑ j ∈ insert i s, a j :=
      Finset.sum_nonneg (fun j hj => (ha j hj).1)
    apply small_nonnegative_close hε hL hnon
    · rw [Finset.sum_insert hi]
      linarith [hai.2]
    · exact hq _ (Finset.Subset.refl _)

/-- One subset is one Boolean query; all queries share the same residual vector. -/
def booleanError {ι : Type*} [Fintype ι] (L ε : ℝ) (a : ι → ℝ) : Prop :=
  ∀ s : Finset ι, circularError L (∑ i ∈ s, a i) ≤ ε

/-- The two signed masses of a residual vector. -/
def signedBody {ι : Type*} [Fintype ι] (ε : ℝ) (a : ι → ℝ) : Prop :=
  (∑ i, max (a i) 0) ≤ ε ∧ (∑ i, max (-a i) 0) ≤ ε

/-- Exact error fiber on principal representatives, for every finite dimension. -/
theorem exact_error_fiber {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L ε : ℝ} (hε : 0 ≤ ε) (hL : 3 * ε < L) (a : ι → ℝ)
    (ha : ∀ i, |a i| ≤ L / 2) : booleanError L ε a ↔ signedBody ε a := by
  have hLp : 0 < L := by linarith
  have hnorm (t : ℝ) (ht : |t| ≤ L / 2) : circularError L t = |t| := by
    exact (AddCircle.norm_coe_eq_abs_iff L hLp.ne').mpr (by simpa [abs_of_pos hLp] using ht)
  constructor
  · intro hq
    have hsmall (i : ι) : |a i| ≤ ε := by
      have hh := hq {i}
      simpa [Finset.sum_singleton, hnorm (a i) (ha i)] using hh
    have positive : ∑ i, max (a i) 0 ≤ ε := by
      let s := Finset.univ.filter (fun i => 0 ≤ a i)
      have heq : (∑ i ∈ s, a i) = ∑ i, max (a i) 0 := by
        simp only [s, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs with hi
        · exact (max_eq_left hi).symm
        · exact (max_eq_right (le_of_not_ge hi)).symm
      rw [← heq]
      exact nonnegative_sum_no_wrap s a hε hL
        (fun i hi => ⟨(Finset.mem_filter.mp hi).2, (le_abs_self _).trans (hsmall i)⟩)
        (fun t _ => hq t)
    have negative : ∑ i, max (-a i) 0 ≤ ε := by
      let s := Finset.univ.filter (fun i => 0 ≤ -a i)
      have heq : (∑ i ∈ s, -a i) = ∑ i, max (-a i) 0 := by
        simp only [s, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs with hi
        · exact (max_eq_left hi).symm
        · exact (max_eq_right (le_of_not_ge hi)).symm
      rw [← heq]
      apply nonnegative_sum_no_wrap s (fun i => -a i) hε hL
      · intro i hi
        exact ⟨(Finset.mem_filter.mp hi).2, (neg_le_abs _).trans (hsmall i)⟩
      · intro t _
        simpa [circularError, Finset.sum_neg_distrib] using hq t
    exact ⟨positive, negative⟩
  · rintro ⟨hp, hn⟩ s
    have upper : (∑ i ∈ s, a i) ≤ ε := calc
      _ ≤ ∑ i ∈ s, max (a i) 0 := Finset.sum_le_sum (fun i _ => le_max_left _ _)
      _ ≤ ∑ i, max (a i) 0 := Finset.sum_le_univ_sum_of_nonneg (fun i => le_max_right _ _)
      _ ≤ ε := hp
    have lower : (∑ i ∈ s, -a i) ≤ ε := calc
      _ ≤ ∑ i ∈ s, max (-a i) 0 := Finset.sum_le_sum (fun i _ => le_max_left _ _)
      _ ≤ ∑ i, max (-a i) 0 := Finset.sum_le_univ_sum_of_nonneg (fun i => le_max_right _ _)
      _ ≤ ε := hn
    have hab : |∑ i ∈ s, a i| ≤ ε := by
      rw [Finset.sum_neg_distrib] at lower
      exact abs_le.mpr ⟨by linarith, upper⟩
    exact (show circularError L (∑ i ∈ s, a i) ≤ |∑ i ∈ s, a i| from
      QuotientAddGroup.norm_mk_le_norm).trans hab

end D5.S3.Geometry.BooleanRotationCodebook
