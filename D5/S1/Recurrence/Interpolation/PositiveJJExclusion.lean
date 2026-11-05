/- GID: D5/S1/Recurrence/Interpolation/PositiveJJExclusion
   generality: I
   mirror-B: D5/B/S1/Recurrence/Interpolation/PositiveJJExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive Fibonacci reciprocal data cannot interpolate across the original JJ clocks. -/

import D5.S1.Recurrence.BilateralLiftUniqueness
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-! Reciprocal interpolation at the two original-clock blocks of a positive JJ word. -/

noncomputable section

open Polynomial Finset Set

namespace D5.S1.Recurrence.Interpolation.PositiveJJExclusion

private lemma spectral (u : ℕ → ℝ)
    (hr : ∀ k, u (k + 2) = u (k + 1) + u k) :
    ∃ A B : ℝ, ∀ k, u k = A * Real.goldenRatio ^ k + B * Real.goldenConj ^ k := by
  have hu : u ∈ (Real.fibRec : LinearRecurrence ℝ).solSpace := by
    change (Real.fibRec : LinearRecurrence ℝ).IsSolution u
    intro k
    change u (k + 2) = ∑ i : Fin 2, ![(1 : ℝ), 1] i * u (k + i)
    simpa [Fin.sum_univ_two, add_comm] using hr k
  rw [D5.S1.Recurrence.fibonacci_solution_space_eq_span,
    Submodule.mem_span_pair] at hu
  obtain ⟨a, b, hab⟩ := hu
  refine ⟨a * Real.goldenRatio, b * Real.goldenConj, fun k => ?_⟩
  have h := congr_fun hab k
  simpa [D5.S1.Recurrence.expandingSequence, D5.S1.Recurrence.contractingSequence,
    pow_succ, mul_assoc, mul_comm, mul_left_comm] using h.symm

private lemma block_count (f w : ℝ → ℝ) (Q : ℝ[X]) (hQ : Q ≠ 0)
    (hd : ∀ t, HasDerivAt f (w t * Q.eval t) t) (hw : ∀ t, w t ≠ 0)
    (L level : ℝ) (n : ℕ)
    (hs : ∀ i : Fin n, (f (L + i) - level) * (f (L + i + 1) - level) < 0) :
    n ≤ (Q.roots.toFinset.filter (fun t => L < t ∧ t < L + n)).card + 1 := by
  classical
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  have hex (i : Fin n) : ∃ z, z ∈ Ioo (L + i) (L + i + 1) ∧ f z = level := by
    rcases mul_neg_iff.mp (hs i) with h | h
    · exact intermediate_value_Ioo' (by linarith) hf.continuousOn
        ⟨by linarith [h.2], by linarith [h.1]⟩
    · exact intermediate_value_Ioo (by linarith) hf.continuousOn
        ⟨by linarith [h.1], by linarith [h.2]⟩
  choose z hz hzv using hex
  have hzinj : Function.Injective z := by
    intro i j hij
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij' | hji'
    · have hle : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij'
      have hi := (hz i).2
      have hj := (hz j).1
      rw [hij] at hi
      linarith
    · have hle : (j : ℝ) + 1 ≤ i := by exact_mod_cast hji'
      have hi := (hz i).1
      have hj := (hz j).2
      rw [hij] at hi
      linarith
  let Z : Finset ℝ := Finset.univ.image z
  have hZ : Z.card = n := by simp [Z, Finset.card_image_of_injective _ hzinj]
  apply hZ.symm.trans_le
  apply Finset.card_le_of_interleaved
  intro x hx y hy hxy _
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨t, ht, hdt⟩ := exists_hasDerivAt_eq_zero hxy hf.continuousOn
    ((hzv i).trans (hzv j).symm) (fun t _ => hd t)
  have hroot : Q.eval t = 0 := (mul_eq_zero.mp hdt).resolve_left (hw t)
  refine ⟨t, Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩, ht.1, ht.2⟩
  · exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hQ).mpr hroot)
  · have hi : (0 : ℝ) ≤ i := by positivity
    linarith [(hz i).1, ht.1]
  · have hj : (j : ℝ) + 1 ≤ n := by exact_mod_cast j.isLt
    linarith [(hz j).2, ht.2]

private def weighted (R : ℝ[X]) (t : ℝ) : ℝ :=
  Real.exp (Real.log Real.goldenRatio * t) * R.eval t

private lemma weighted_nat (R : ℝ[X]) (k : ℕ) :
    weighted R k = Real.goldenRatio ^ k * R.eval (k : ℝ) := by
  simp [weighted, mul_comm (Real.log _), Real.exp_nat_mul,
    Real.exp_log Real.goldenRatio_pos]

private lemma weighted_derivative (R : ℝ[X]) (t : ℝ) :
    HasDerivAt (weighted R)
      (Real.exp (Real.log Real.goldenRatio * t) *
        (R.derivative + C (Real.log Real.goldenRatio) * R).eval t) t := by
  change HasDerivAt (fun x : ℝ => Real.exp (Real.log Real.goldenRatio * x) * R.eval x) _ t
  convert (((hasDerivAt_id t).const_mul (Real.log Real.goldenRatio)).exp.mul
    (R.hasDerivAt t)) using 1
  all_goals first | rfl | (simp only [id_eq, mul_one, eval_add, eval_mul, eval_C]; ring)

private lemma weighted_polynomial (R : ℝ[X]) (hR : R ≠ 0) :
    (R.derivative + C (Real.log Real.goldenRatio) * R) ≠ 0 ∧
    (R.derivative + C (Real.log Real.goldenRatio) * R).natDegree ≤ R.natDegree := by
  have hc : Real.log Real.goldenRatio ≠ 0 :=
    ne_of_gt (Real.log_pos Real.one_lt_goldenRatio)
  have htop : (R.derivative + C (Real.log Real.goldenRatio) * R).coeff R.natDegree =
      Real.log Real.goldenRatio * R.leadingCoeff := by
    simp [coeff_derivative, coeff_eq_zero_of_natDegree_lt
      (show R.natDegree < R.natDegree + 1 by omega)]
  constructor
  · intro hz
    have := mul_ne_zero hc (Polynomial.leadingCoeff_ne_zero.mpr hR)
    rw [hz, coeff_zero] at htop
    exact this htop.symm
  · exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_derivative_le R).trans (Nat.sub_le _ _)) (natDegree_C_mul_le _ _))

private lemma initial_cross (R : ℝ[X]) (u : ℕ → ℝ) (k shift : ℕ)
    (hs : u k * u (k + 1) < 0)
    (h0 : u k * R.eval ((k + shift : ℕ) : ℝ) = 1)
    (h1 : u (k + 1) * R.eval ((k + 1 + shift : ℕ) : ℝ) = 1) :
    weighted R (k + shift : ℕ) * weighted R (k + 1 + shift : ℕ) < 0 := by
  have he : (u k * u (k + 1)) *
      (R.eval ((k + shift : ℕ) : ℝ) * R.eval ((k + 1 + shift : ℕ) : ℝ)) = 1 := by
    nlinarith [congrArg₂ (fun x y : ℝ => x * y) h0 h1]
  have hv : R.eval ((k + shift : ℕ) : ℝ) * R.eval ((k + 1 + shift : ℕ) : ℝ) < 0 := by
    by_contra! hv
    have hn := mul_nonpos_of_nonpos_of_nonneg hs.le hv
    linarith
  dsimp [weighted]
  have hp0 := Real.exp_pos (Real.log Real.goldenRatio * ((k + shift : ℕ) : ℝ))
  have hp1 := Real.exp_pos (Real.log Real.goldenRatio * ((k + 1 + shift : ℕ) : ℝ))
  calc
    _ = (Real.exp (Real.log Real.goldenRatio * ((k + shift : ℕ) : ℝ)) *
        Real.exp (Real.log Real.goldenRatio * ((k + 1 + shift : ℕ) : ℝ))) *
        (R.eval ((k + shift : ℕ) : ℝ) * R.eval ((k + 1 + shift : ℕ) : ℝ)) := by ring
    _ < 0 := mul_neg_of_pos_of_neg (mul_pos hp0 hp1) hv

private lemma tail_cross (R : ℝ[X]) (u : ℕ → ℝ) (A B : ℝ) (hB : 0 < B)
    (hu : ∀ k, u k = A * Real.goldenRatio ^ k + B * Real.goldenConj ^ k)
    (k shift : ℕ) (ha0 : 0 < A * u k) (ha1 : 0 < A * u (k + 1))
    (h0 : u k * R.eval ((k + shift : ℕ) : ℝ) = 1)
    (h1 : u (k + 1) * R.eval ((k + 1 + shift : ℕ) : ℝ) = 1) :
    (weighted R (k + shift : ℕ) - Real.goldenRatio ^ shift / A) *
      (weighted R (k + 1 + shift : ℕ) - Real.goldenRatio ^ shift / A) < 0 := by
  have hA : A ≠ 0 := by rintro rfl; simp at ha0
  have ident (j : ℕ) (hj : u j * R.eval ((j + shift : ℕ) : ℝ) = 1) :
      (A * u j) * (weighted R (j + shift : ℕ) - Real.goldenRatio ^ shift / A) =
        -(Real.goldenRatio ^ shift * B * Real.goldenConj ^ j) := by
    rw [weighted_nat, pow_add]
    calc
      _ = Real.goldenRatio ^ shift *
          (A * Real.goldenRatio ^ j * (u j * R.eval ((j + shift : ℕ) : ℝ)) - u j) := by
        field_simp [hA]
      _ = Real.goldenRatio ^ shift * (A * Real.goldenRatio ^ j - u j) := by rw [hj]; ring
      _ = _ := by rw [hu j]; ring
  have e0 := ident k h0
  have e1 := ident (k + 1) h1
  have hp : 0 < (Real.goldenRatio ^ shift * B * Real.goldenConj ^ k) ^ 2 :=
    sq_pos_of_ne_zero (mul_ne_zero (mul_ne_zero
      (pow_ne_zero _ Real.goldenRatio_ne_zero) hB.ne')
      (pow_ne_zero _ Real.goldenConj_ne_zero))
  have hn : -(Real.goldenRatio ^ shift * B * Real.goldenConj ^ k) *
      -(Real.goldenRatio ^ shift * B * Real.goldenConj ^ (k + 1)) < 0 := by
    calc
      _ = (Real.goldenRatio ^ shift * B * Real.goldenConj ^ k) ^ 2 * Real.goldenConj := by
        rw [pow_succ]; ring
      _ < 0 := mul_neg_of_pos_of_neg hp Real.goldenConj_neg
  have he : (A * u k) * (A * u (k + 1)) *
      ((weighted R (k + shift : ℕ) - Real.goldenRatio ^ shift / A) *
        (weighted R (k + 1 + shift : ℕ) - Real.goldenRatio ^ shift / A)) < 0 := by
    calc
      _ = ((A * u k) * (weighted R (k + shift : ℕ) - Real.goldenRatio ^ shift / A)) *
          ((A * u (k + 1)) *
            (weighted R (k + 1 + shift : ℕ) - Real.goldenRatio ^ shift / A)) := by ring
      _ < 0 := by rw [e0, e1]; exact hn
  exact (mul_neg_iff.mp he).resolve_right (by intro h; linarith [mul_pos ha0 ha1]) |>.2

private lemma positive_tail (u : ℕ → ℝ) (A B : ℝ)
    (hu : ∀ k, u k = A * Real.goldenRatio ^ k + B * Real.goldenConj ^ k)
    (hr : ∀ k, u (k + 2) = u (k + 1) + u k) (s : ℕ)
    (hs : 0 < u s * u (s + 1)) : ∀ k, s ≤ k → 0 < A * u k := by
  have hid : u (s + 1) - Real.goldenConj * u s =
      A * Real.goldenRatio ^ s * (Real.goldenRatio - Real.goldenConj) := by
    rw [hu (s + 1), hu s, pow_succ, pow_succ]
    ring
  have hc : 0 < Real.goldenRatio ^ s * (Real.goldenRatio - Real.goldenConj) :=
    mul_pos (pow_pos Real.goldenRatio_pos _)
      (sub_pos.mpr (lt_trans Real.goldenConj_neg Real.goldenRatio_pos))
  have hAs : 0 < A * u s := by
    apply (mul_pos_iff_of_pos_right hc).mp
    calc
      _ = u s * (u (s + 1) - Real.goldenConj * u s) := by rw [hid]; ring
      _ > 0 := by
        have hn := mul_nonpos_of_nonpos_of_nonneg Real.goldenConj_neg.le (sq_nonneg (u s))
        nlinarith
  have hus : u s ≠ 0 := by intro h; simp [h] at hs
  have hAs1 : 0 < A * u (s + 1) := by
    have hp := mul_pos hAs hs
    have he : (A * u s) * (u s * u (s + 1)) = (u s) ^ 2 * (A * u (s + 1)) := by ring
    rw [he] at hp
    exact (mul_pos_iff_of_pos_left (sq_pos_of_ne_zero hus)).mp hp
  have hall (n : ℕ) : 0 < A * u (s + n) := by
    induction n using Nat.twoStepInduction with
    | zero => simpa using hAs
    | one => simpa using hAs1
    | more n hn hn1 =>
      rw [show s + (n + 2) = (s + n) + 2 by omega, hr, mul_add]
      exact add_pos (by simpa [Nat.add_assoc] using hn1) hn
  intro k hk
  simpa [Nat.add_sub_of_le hk] using hall (k - s)

private lemma three_blocks (f w : ℝ → ℝ) (Q : ℝ[X]) (hQ : Q ≠ 0)
    (hd : ∀ t, HasDerivAt f (w t * Q.eval t) t) (hw : ∀ t, w t ≠ 0)
    (L₀ L₁ L₂ c₀ c₁ c₂ : ℝ) (n₀ n₁ n₂ : ℕ)
    (h01 : L₀ + n₀ ≤ L₁) (h12 : L₁ + n₁ ≤ L₂)
    (hs0 : ∀ i : Fin n₀, (f (L₀ + i) - c₀) * (f (L₀ + i + 1) - c₀) < 0)
    (hs1 : ∀ i : Fin n₁, (f (L₁ + i) - c₁) * (f (L₁ + i + 1) - c₁) < 0)
    (hs2 : ∀ i : Fin n₂, (f (L₂ + i) - c₂) * (f (L₂ + i + 1) - c₂) < 0) :
    n₀ + n₁ + n₂ ≤ Q.natDegree + 3 := by
  classical
  let Z₀ := Q.roots.toFinset.filter (fun t => L₀ < t ∧ t < L₀ + n₀)
  let Z₁ := Q.roots.toFinset.filter (fun t => L₁ < t ∧ t < L₁ + n₁)
  let Z₂ := Q.roots.toFinset.filter (fun t => L₂ < t ∧ t < L₂ + n₂)
  have h0 := block_count f w Q hQ hd hw L₀ c₀ n₀ hs0
  have h1 := block_count f w Q hQ hd hw L₁ c₁ n₁ hs1
  have h2 := block_count f w Q hQ hd hw L₂ c₂ n₂ hs2
  have d01 : Disjoint Z₀ Z₁ := by
    apply Finset.disjoint_left.mpr
    intro t ht hu
    have ht := (Finset.mem_filter.mp ht).2
    have hu := (Finset.mem_filter.mp hu).2
    linarith
  have d12 : Disjoint Z₁ Z₂ := by
    apply Finset.disjoint_left.mpr
    intro t ht hu
    have ht := (Finset.mem_filter.mp ht).2
    have hu := (Finset.mem_filter.mp hu).2
    linarith
  have d02 : Disjoint Z₀ Z₂ := by
    apply Finset.disjoint_left.mpr
    intro t ht hu
    have ht := (Finset.mem_filter.mp ht).2
    have hu := (Finset.mem_filter.mp hu).2
    have hn : (0 : ℝ) ≤ n₁ := by positivity
    linarith
  have hcard : Z₀.card + Z₁.card + Z₂.card ≤ Q.natDegree := by
    calc
      _ = ((Z₀ ∪ Z₁) ∪ Z₂).card := by
        rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨d02, d12⟩),
          Finset.card_union_of_disjoint d01]
      _ ≤ Q.roots.toFinset.card := Finset.card_le_card (Finset.union_subset
        (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
        (Finset.filter_subset _ _))
      _ ≤ Q.natDegree := (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' Q)
  change n₀ ≤ Z₀.card + 1 at h0
  change n₁ ≤ Z₁.card + 1 at h1
  change n₂ ≤ Z₂.card + 1 at h2
  omega

/-- No polynomial of degree at most `m - 1` interpolates the full positive JJ data
at the original clocks, including both occurrences of the transition exponent. -/
theorem positive_jj_exclusion (m a : ℕ) (ρ : ℝ) (u : ℕ → ℝ)
    (hm : 5 ≤ m) (ha : a ≤ 2 * m - 2) (hρ : 0 < ρ)
    (hu0 : u 0 = 1) (hu1 : u 1 = -ρ)
    (hr : ∀ k, u (k + 2) = u (k + 1) + u k) :
    ¬ ∃ R : ℝ[X], R.natDegree ≤ m - 1 ∧
      (∀ k, k ≤ 2 * m - 2 → u k ≠ 0) ∧
      (∀ k, k ≤ a → u k * R.eval (k : ℝ) = 1) ∧
      (∀ k, a ≤ k → k ≤ 2 * m - 2 → u k * R.eval ((k + 2 : ℕ) : ℝ) = 1) := by
  classical
  rintro ⟨R, hdeg, hn, hp, ht⟩
  let K := 2 * m - 2
  have haK : a ≤ K := ha
  have hR0 : R.eval 0 = 1 := by simpa [hu0] using hp 0 (Nat.zero_le a)
  have hR : R ≠ 0 := by intro h; simp [h] at hR0
  let Q := R.derivative + C (Real.log Real.goldenRatio) * R
  obtain ⟨hQ, hQdeg⟩ := weighted_polynomial R hR
  change Q ≠ 0 at hQ
  change Q.natDegree ≤ R.natDegree at hQdeg
  let w : ℝ → ℝ := fun t => Real.exp (Real.log Real.goldenRatio * t)
  have hd (t : ℝ) : HasDerivAt (weighted R) (w t * Q.eval t) t :=
    weighted_derivative R t
  have hw (t : ℝ) : w t ≠ 0 := Real.exp_ne_zero _
  obtain ⟨A, B, hu⟩ := spectral u hr
  have hB : 0 < B := by
    have h0 := hu 0
    have h1 := hu 1
    simp only [pow_zero, mul_one, hu0, pow_one, hu1] at h0 h1
    have hdif : 0 < Real.goldenRatio - Real.goldenConj :=
      sub_pos.mpr (lt_trans Real.goldenConj_neg Real.goldenRatio_pos)
    have hid : B * (Real.goldenRatio - Real.goldenConj) = Real.goldenRatio + ρ := by
      have he := congrArg (fun x : ℝ => x * Real.goldenRatio) h0
      nlinarith only [he, h1]
    exact (mul_pos_iff_of_pos_right hdif).mp (by rw [hid]; positivity)
  obtain ⟨s, hsK, hbefore, hafter⟩ : ∃ s : ℕ, s ≤ K ∧
      (∀ k, k < s → u k * u (k + 1) < 0) ∧
      (s < K → ∀ k, s ≤ k → 0 < A * u k) := by
    by_cases he : ∃ j : ℕ, j < K ∧ 0 < u j * u (j + 1)
    · let s := Nat.find he
      have hs := Nat.find_spec he
      refine ⟨s, hs.1.le, ?_, fun _ => positive_tail u A B hu hr s hs.2⟩
      intro k hk
      have hnot : ¬ 0 < u k * u (k + 1) := by
        intro hpos
        exact Nat.find_min he hk ⟨by omega, hpos⟩
      have hne : u k * u (k + 1) ≠ 0 :=
        mul_ne_zero (hn k (by omega)) (hn (k + 1) (by omega))
      exact (lt_or_gt_of_ne hne).resolve_right hnot
    · refine ⟨K, le_rfl, ?_, by omega⟩
      intro k hk
      have hnot : ¬ 0 < u k * u (k + 1) := fun hpos => he ⟨k, hk, hpos⟩
      have hne : u k * u (k + 1) ≠ 0 :=
        mul_ne_zero (hn k (by omega)) (hn (k + 1) (by omega))
      exact (lt_or_gt_of_ne hne).resolve_right hnot
  have hpi (k : ℕ) (hks : k < s) (hka : k + 1 ≤ a) :
      weighted R k * weighted R (k + 1 : ℕ) < 0 := by
    simpa using initial_cross R u k 0 (hbefore k hks)
      (by simpa using hp k (by omega)) (by simpa using hp (k + 1) hka)
  have hti (k : ℕ) (hks : k < s) (hak : a ≤ k) :
      weighted R (k + 2 : ℕ) * weighted R (k + 3 : ℕ) < 0 := by
    simpa [Nat.add_assoc] using initial_cross R u k 2 (hbefore k hks)
      (ht k hak (by omega)) (ht (k + 1) (by omega) (by omega))
  have hpt (k : ℕ) (hsk : s ≤ k) (hka : k + 1 ≤ a) :
      (weighted R k - 1 / A) * (weighted R (k + 1 : ℕ) - 1 / A) < 0 := by
    have hslt : s < K := by omega
    simpa using tail_cross R u A B hB hu k 0
      (hafter hslt k hsk) (hafter hslt (k + 1) (by omega))
      (by simpa using hp k (by omega)) (by simpa using hp (k + 1) hka)
  have htt (k : ℕ) (hsk : s ≤ k) (hak : a ≤ k) (hkK : k < K) :
      (weighted R (k + 2 : ℕ) - Real.goldenRatio ^ 2 / A) *
        (weighted R (k + 3 : ℕ) - Real.goldenRatio ^ 2 / A) < 0 := by
    have hslt : s < K := by omega
    simpa [Nat.add_assoc] using tail_cross R u A B hB hu k 2
      (hafter hslt k hsk) (hafter hslt (k + 1) (by omega))
      (ht k hak (by omega)) (ht (k + 1) (by omega) (by omega))
  have hcount : K ≤ Q.natDegree + 3 := by
    by_cases hsa : s ≤ a
    · have hc := three_blocks (weighted R) w Q hQ hd hw
        0 s (a + 2 : ℕ) 0 (1 / A) (Real.goldenRatio ^ 2 / A) s (a - s) (K - a)
        (by simp) (by exact_mod_cast (show s + (a - s) ≤ a + 2 by omega))
        (by
          intro i
          simpa using hpi i i.isLt (by omega))
        (by
          intro i
          have hi := i.isLt
          simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm,
            show (1 : ℝ) + 2 = 3 by norm_num] using
            hpt (s + i) (by omega) (by omega))
        (by
          intro i
          have hi := i.isLt
          simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm,
            show (1 : ℝ) + 2 = 3 by norm_num] using
            htt (a + i) (by omega) (by omega) (by omega))
      omega
    · have hc := three_blocks (weighted R) w Q hQ hd hw
        0 (a + 2 : ℕ) (s + 2 : ℕ) 0 0 (Real.goldenRatio ^ 2 / A) a (s - a) (K - s)
        (by push_cast; linarith)
        (by exact_mod_cast (show a + 2 + (s - a) ≤ s + 2 by omega))
        (by
          intro i
          simpa using hpi i (by omega) (by omega))
        (by
          intro i
          have hi := i.isLt
          simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm,
            show (1 : ℝ) + 2 = 3 by norm_num] using
            hti (a + i) (by omega) (by omega))
        (by
          intro i
          have hi := i.isLt
          simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm,
            show (1 : ℝ) + 2 = 3 by norm_num] using
            htt (s + i) (by omega) (by omega) (by omega))
      omega
  dsimp [K] at hcount
  omega

#print axioms positive_jj_exclusion

end D5.S1.Recurrence.Interpolation.PositiveJJExclusion
