import Mathlib.Tactic
import OmegaBuild.Commands

/-!
# Attainable second moments of finite positive weighted sums

Omega original. Positivity forces the normalized first moment inside the support
interval. Its location determines the exact range of second moments and the
minimum number of distinct support points.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Omega.MeasureTheory.FiniteWeightedSecondMoment

open scoped BigOperators

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Realize three scalar moments by distinct nodes with positive weights. -/
def HasMoments (n : ℕ) (a b M x s : K) : Prop :=
  ∃ t w : Fin n → K, Function.Injective t ∧
    (∀ i, a < t i ∧ t i < b) ∧ (∀ i, 0 < w i) ∧
    (∑ i, w i * t i ^ 0) = M ∧ (∑ i, w i * t i ^ 1) = M * x ∧ (∑ i, w i * t i ^ 2) = s

private theorem moment_bounds {n : ℕ} {a b M x s : K}
    (hM : 0 < M) (h : HasMoments n a b M x s) :
    a < x ∧ x < b ∧ M * x ^ 2 ≤ s ∧ s < M * ((a + b) * x - a * b) ∧
      (s = M * x ^ 2 ↔ n = 1) := by
  obtain ⟨t, w, ht, hnodes, hw, h₀, h₁, h₂⟩ := h
  have hmass : ∑ i, w i = M := by simpa using h₀
  have hfirst : ∑ i, w i * t i = M * x := by simpa using h₁
  have hsecond : ∑ i, w i * t i ^ 2 = s := h₂
  have hn : 0 < n := by
    by_contra! hn
    obtain rfl : n = 0 := by omega
    simp at hmass
    exact (ne_of_gt hM) hmass.symm
  let first : Fin n := ⟨0, hn⟩
  have hleft : M * a < M * x := by
    have hpos (i : Fin n) : 0 < w i * (t i - a) := mul_pos (hw i) (sub_pos.mpr (hnodes i).1)
    have hsum := Finset.sum_pos' (s := Finset.univ) (fun i _ => (hpos i).le)
      ⟨first, Finset.mem_univ _, hpos first⟩
    simpa only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, hfirst, sub_pos] using hsum
  have hright : M * x < M * b := by
    have hpos (i : Fin n) : 0 < w i * (b - t i) := mul_pos (hw i) (sub_pos.mpr (hnodes i).2)
    have hsum := Finset.sum_pos' (s := Finset.univ) (fun i _ => (hpos i).le)
      ⟨first, Finset.mem_univ _, hpos first⟩
    simpa only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, hfirst, sub_pos] using hsum
  have hvariance : (∑ i, w i * (t i - x) ^ 2) = s - M * x ^ 2 := by
    calc
      _ = ∑ i, (w i * t i ^ 2 - (2 * x) * (w i * t i) + x ^ 2 * w i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          hmass, hfirst, hsecond]
        ring
  have hgap : (∑ i, w i * ((t i - a) * (b - t i))) = M * ((a + b) * x - a * b) - s := by
    calc
      _ = ∑ i, ((a + b) * (w i * t i) - (a * b) * w i - w i * t i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hmass, hfirst, hsecond]
        ring
  have hterm (i : Fin n) : 0 ≤ w i * (t i - x) ^ 2 :=
    mul_nonneg (hw i).le (sq_nonneg _)
  refine ⟨(mul_lt_mul_iff_right₀ hM).mp hleft, (mul_lt_mul_iff_right₀ hM).mp hright,
    sub_nonneg.mp (hvariance ▸ Finset.sum_nonneg fun i _ => hterm i), ?_, ?_⟩
  · apply sub_pos.mp
    rw [← hgap]
    have hpositive (i : Fin n) : 0 < w i * ((t i - a) * (b - t i)) :=
      mul_pos (hw i) (mul_pos (sub_pos.mpr (hnodes i).1) (sub_pos.mpr (hnodes i).2))
    exact Finset.sum_pos' (fun i _ => (hpositive i).le)
      ⟨first, Finset.mem_univ _, hpositive first⟩
  · constructor
    · intro hs
      have hzero : ∑ i, w i * (t i - x) ^ 2 = 0 := by rw [hvariance, hs, sub_self]
      have htmean (i : Fin n) : t i = x := by
        have hle := Finset.single_le_sum (f := fun i => w i * (t i - x) ^ 2)
          (fun i _ => hterm i) (Finset.mem_univ i)
        rw [hzero] at hle
        rcases mul_eq_zero.mp (le_antisymm hle (hterm i)) with hwi | hi
        · exact ((ne_of_gt (hw i)) hwi).elim
        · exact sub_eq_zero.mp (by nlinarith only [hi, sq_nonneg (t i - x)])
      by_contra hne
      let second : Fin n := ⟨1, by omega⟩
      have heq : first = second := ht ((htmean first).trans (htmean second).symm)
      have := congrArg Fin.val heq
      contradiction
    · rintro rfl
      simp at hmass hfirst hsecond
      have hnode : t 0 = x := by
        apply mul_left_cancel₀ (ne_of_gt hM)
        simpa [hmass] using hfirst
      simpa [hmass, hnode] using hsecond.symm

omit [IsStrictOrderedRing K] in
private theorem one_node {a b M x : K} (hM : 0 < M) (ha : a < x) (hb : x < b) :
    HasMoments 1 a b M x (M * x ^ 2) := by
  refine ⟨fun _ => x, fun _ => M, ?_, fun _ => ⟨ha, hb⟩, fun _ => hM, ?_, ?_, ?_⟩
  · exact fun _ _ _ => Subsingleton.elim _ _
  · simp
  · simp
  · simp

private theorem two_nodes {a b M x s : K} (hM : 0 < M) (ha : a < x) (hb : x < b)
    (hs : M * x ^ 2 < s) (hupper : s < M * ((a + b) * x - a * b)) :
    HasMoments 2 a b M x s := by
  let v := s / M - x ^ 2
  have hv : 0 < v := sub_pos.mpr ((lt_div_iff₀ hM).mpr (by simpa [mul_comm] using hs))
  have hvlt : v < (x - a) * (b - x) := by
    have h := (div_lt_iff₀ hM).mpr (by simpa [mul_comm] using hupper)
    dsimp [v]
    linarith only [h, show (a + b) * x - a * b = x ^ 2 + (x - a) * (b - x) by ring]
  have hleft : v / (b - x) < x - a := (div_lt_iff₀ (sub_pos.mpr hb)).mpr hvlt
  let d := (v / (b - x) + (x - a)) / 2
  have hd₁ : v / (b - x) < d := by dsimp [d]; linarith
  have hd₂ : d < x - a := by dsimp [d]; linarith
  have hd : 0 < d := (div_pos hv (sub_pos.mpr hb)).trans hd₁
  let e := v / d
  have he : 0 < e := div_pos hv hd
  have helt : e < b - x := (div_lt_iff₀ hd).mpr (by
    rw [mul_comm]
    exact (div_lt_iff₀ (sub_pos.mpr hb)).mp hd₁)
  have hwidth : 0 < d + e := add_pos hd he
  have hprod : d * e = v := by
    dsimp [e]
    field_simp [ne_of_gt hd]
  have hmoment : M * (x ^ 2 + d * e) = s := by
    rw [hprod]
    dsimp [v]
    field_simp [ne_of_gt hM]
    ring
  let t : Fin 2 → K := ![x - d, x + e]
  let w : Fin 2 → K := ![M * e / (d + e), M * d / (d + e)]
  have hdistinct : x - d < x + e := by linarith
  refine ⟨t, w, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact (ne_of_lt hdistinct hij).elim
    · exact (ne_of_lt hdistinct hij.symm).elim
    · rfl
  · intro i
    fin_cases i
    · change a < x - d ∧ x - d < b
      constructor <;> linarith
    · change a < x + e ∧ x + e < b
      exact ⟨ha.trans (lt_add_of_pos_right x he), by linarith⟩
  · intro i
    fin_cases i
    · exact div_pos (mul_pos hM he) hwidth
    · exact div_pos (mul_pos hM hd) hwidth
  · simp [Fin.sum_univ_two, w]
    field_simp [ne_of_gt hwidth]
    ring
  · simp [Fin.sum_univ_two, w, t]
    field_simp [ne_of_gt hwidth]
    ring
  · rw [← hmoment]
    simp [Fin.sum_univ_two, w, t]
    field_simp [ne_of_gt hwidth]
    ring

/-- The feasible means, second moments and minimum number of distinct nodes. -/
theorem finite_weighted_second_moment_range {a b M x s : K} (hM : 0 < M) :
    (∀ n, HasMoments n a b M x s →
      a < x ∧ x < b ∧ M * x ^ 2 ≤ s ∧ s < M * ((a + b) * x - a * b) ∧
        (s = M * x ^ 2 ↔ n = 1)) ∧
    (a < x ∧ x < b ∧ M * x ^ 2 ≤ s ∧ s < M * ((a + b) * x - a * b) →
      HasMoments (if s = M * x ^ 2 then 1 else 2) a b M x s) := by
  refine ⟨fun _ h => moment_bounds hM h, fun ⟨ha, hb, hlower, hupper⟩ => ?_⟩
  by_cases hs : s = M * x ^ 2
  · simpa [hs] using one_node hM ha hb
  · simpa [hs] using two_nodes hM ha hb (lt_of_le_of_ne hlower (Ne.symm hs)) hupper

end Omega.MeasureTheory.FiniteWeightedSecondMoment
