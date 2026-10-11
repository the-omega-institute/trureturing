/- GID: D5/S1/Phase/MultivariateWeylRectangles
   generality: G
   mirror-B: D5/B/S1/Phase/MultivariateWeylRectangles
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Polynomial phase averages over independently growing rectangular boxes. -/

import D5.S1.Phase.CharacterAverage
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous

noncomputable section

namespace D5.S1.Phase.MultivariateWeylRectangles

open Filter Finset
open scoped Topology BigOperators

/-- The phase of an integer polynomial evaluated at one natural-number tuple. -/
def polynomialPhase {d : ℕ} (α : ℝ) (Q : MvPolynomial (Fin d) ℤ)
    (n : Fin d → ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * α *
    (MvPolynomial.eval (fun i => (n i : ℤ)) Q : ℂ))

/-- Cancellation over every sufficiently large rectangle, with a common side threshold. -/
def RectangularCancellation {d : ℕ} (f : (Fin d → ℕ) → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℕ, 1 ≤ R ∧ ∀ N : Fin d → ℕ,
    (∀ i, R ≤ N i) → ‖𝔼 n ∈ Fintype.piFinset (fun i => range (N i)), f n‖ < ε

private theorem norm_expect_sq_le {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖𝔼 n ∈ s, f n‖ ^ 2 ≤ 𝔼 n ∈ s, ‖f n‖ ^ 2 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  calc
    _ ≤ (𝔼 n ∈ s, ‖f n‖) ^ 2 := by
      gcongr
      exact RCLike.norm_expect_le (K := ℂ)
    _ ≤ _ := by
      simpa [Finset.expect_const hs] using
        Finset.expect_mul_sq_le_sq_mul_sq s (fun n => ‖f n‖) (fun _ => (1 : ℝ))

private theorem smoothing_sq_le {ι : Type*} (s : Finset ι) (H : ℕ)
    (z : ι → ℕ → ℂ) :
    ‖𝔼 n ∈ s, 𝔼 h ∈ range H, z n h‖ ^ 2 ≤
      (∑ h ∈ range H, ∑ k ∈ range H,
        (𝔼 n ∈ s, z n h * star (z n k)).re) / (H : ℝ) ^ 2 := by
  apply (norm_expect_sq_le s _).trans_eq
  have heq (n : ι) : ‖𝔼 h ∈ range H, z n h‖ ^ 2 =
      (∑ h ∈ range H, ∑ k ∈ range H,
        (z n h * star (z n k)).re) / (H : ℝ) ^ 2 := by
    rw [expect_eq_sum_div_card, card_range, norm_div, Complex.norm_natCast, div_pow]
    congr 1
    calc
      _ = ((∑ h ∈ range H, z n h) * star (∑ k ∈ range H, z n k)).re := by
        rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      _ = _ := by simp only [star_sum, Finset.sum_mul_sum, Complex.re_sum]
  simp_rw [heq]
  rw [← expect_div]
  congr 1
  simp_rw [expect_sum_comm]
  apply sum_congr rfl
  intro h hh
  apply sum_congr rfl
  intro k hk
  simp only [expect_eq_sum_div_card]
  rw [← Complex.re_sum]
  exact (Complex.div_ofReal_re _ (s.card : ℝ)).symm

private theorem cancellation_of_correlations {ι β : Type*} (l : Filter β)
    (s : β → Finset ι) (f : ι → ℂ) (z : ι → ℕ → ℂ)
    (hne : ∀ᶠ b in l, (s b).Nonempty)
    (hunit : ∀ n h, ‖z n h‖ = 1)
    (hshift : ∀ h, Tendsto (fun b => (𝔼 n ∈ s b, z n h) - (𝔼 n ∈ s b, f n)) l (𝓝 0))
    (hcorr : ∀ h k, h ≠ k →
      Tendsto (fun b => 𝔼 n ∈ s b, z n h * star (z n k)) l (𝓝 0)) :
    Tendsto (fun b => 𝔼 n ∈ s b, f n) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨H, hHpos, hHsmall⟩ := Real.exists_nat_pos_inv_lt (by positivity : 0 < ε ^ 2 / 4)
  have hHne : H ≠ 0 := by omega
  have hHreal : (H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hHne
  have hHcomplex : (H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hHne
  have hgap : Tendsto (fun b =>
      (𝔼 n ∈ s b, 𝔼 h ∈ range H, z n h) - (𝔼 n ∈ s b, f n)) l (𝓝 0) := by
    have hh := (tendsto_finsetSum (range H) (fun h _ => hshift h)).div_const (H : ℂ)
    simpa only [sum_const_zero, zero_div] using hh.congr (fun b => by
      rw [expect_comm]
      simp only [expect_eq_sum_div_card, card_range, sum_sub_distrib, sum_const,
        card_range, nsmul_eq_mul, sub_div, mul_div_cancel_left₀ _ hHcomplex])
  have hlim : Tendsto (fun b =>
      (∑ h ∈ range H, ∑ k ∈ range H,
        (𝔼 n ∈ s b, z n h * star (z n k)).re) / (H : ℝ) ^ 2) l
      (𝓝 ((H : ℝ)⁻¹)) := by
    have ht (h k : ℕ) : Tendsto
        (fun b => (𝔼 n ∈ s b, z n h * star (z n k)).re) l
        (𝓝 (if h = k then (1 : ℝ) else 0)) := by
      by_cases heq : h = k
      · subst k
        apply tendsto_const_nhds.congr'
        filter_upwards [hne] with b hb
        simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hunit,
          Finset.expect_const hb]
      · simpa only [if_neg heq, Complex.zero_re, Function.comp_def] using
          (Complex.continuous_re.tendsto 0).comp (hcorr h k heq)
    have hh := (tendsto_finsetSum (range H) (fun h _ =>
      tendsto_finsetSum (range H) (fun k _ => ht h k))).div_const ((H : ℝ) ^ 2)
    convert hh using 1
    have hdiag : (∑ h ∈ range H, ∑ k ∈ range H,
        if h = k then (1 : ℝ) else 0) = (H : ℝ) := by
      calc
        _ = ∑ h ∈ range H, (1 : ℝ) := sum_congr rfl (fun h hh => by simp [hh])
        _ = _ := by simp
    rw [hdiag]
    field_simp

  have hb := hlim.eventually (gt_mem_nhds hHsmall)
  have hg := (hgap.norm).eventually (gt_mem_nhds (show ‖(0 : ℂ)‖ < ε / 2 by simpa only [norm_zero] using half_pos hε))
  filter_upwards [hb, hg] with b hb hg
  rw [dist_zero_right]
  have hs := smoothing_sq_le (s b) H z
  have hslt : ‖𝔼 n ∈ s b, 𝔼 h ∈ range H, z n h‖ < ε / 2 := by
    nlinarith [norm_nonneg (𝔼 n ∈ s b, 𝔼 h ∈ range H, z n h)]
  have htri := norm_sub_le (𝔼 n ∈ s b, 𝔼 h ∈ range H, z n h)
    ((𝔼 n ∈ s b, 𝔼 h ∈ range H, z n h) - (𝔼 n ∈ s b, f n))
  simp only [sub_sub_cancel] at htri
  linarith

private theorem shifted_interval_average_bound (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (N h : ℕ) :
    ‖(𝔼 n ∈ range N, f (n + h)) - (𝔼 n ∈ range N, f n)‖ ≤ 2 * h / (N : ℝ) := by
  have hid : (∑ n ∈ range N, f (n + h)) - ∑ n ∈ range N, f n =
      (∑ n ∈ range h, f (n + N)) - ∑ n ∈ range h, f n := by
    have h₁ := sum_range_add f N h
    have h₂ := sum_range_add f h N
    rw [Nat.add_comm h N] at h₂
    simp_rw [Nat.add_comm N, Nat.add_comm h] at h₁ h₂
    linear_combination h₁ - h₂
  have hn (a : ℕ) : ‖∑ n ∈ range h, f (n + a)‖ ≤ (h : ℝ) := by
    calc
      _ ≤ ∑ n ∈ range h, ‖f (n + a)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ range h, (1 : ℝ) := sum_le_sum (fun n _ => hf (n + a))
      _ = _ := by simp
  simp only [expect_eq_sum_div_card, card_range, ← sub_div, norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  rw [hid]
  have hn₀ := hn 0
  simp only [Nat.add_zero] at hn₀
  linarith [norm_sub_le (∑ n ∈ range h, f (n + N)) (∑ n ∈ range h, f n), hn N]

private theorem box_average_split {d : ℕ} (N : Fin d → ℕ) (i : Fin d)
    (f : (Fin d → ℕ) → ℂ) :
    (𝔼 n ∈ Fintype.piFinset (fun j => range (N j)), f n) =
      𝔼 y ∈ Fintype.piFinset (fun j : {j : Fin d // j ≠ i} => range (N j)),
        𝔼 x ∈ range (N i), f ((Equiv.funSplitAt i ℕ).symm (x, y)) := by
  classical
  have he := expect_equiv (Equiv.funSplitAt i ℕ)
    (s := Fintype.piFinset (fun j => range (N j)))
    (t := range (N i) ×ˢ Fintype.piFinset (fun j : {j : Fin d // j ≠ i} => range (N j)))
    (f := f) (g := fun p => f ((Equiv.funSplitAt i ℕ).symm p))
    (by
      intro n
      simp only [Fintype.mem_piFinset, mem_product, Equiv.funSplitAt_apply]
      constructor
      · intro hn; exact ⟨hn i, fun j => hn j⟩
      · rintro ⟨hi, hrest⟩ j
        by_cases hj : j = i
        · simpa [hj] using hi
        · exact hrest ⟨j, hj⟩)
    (by intro n _; exact congrArg f ((Equiv.funSplitAt i ℕ).symm_apply_apply n).symm)
  rw [he, expect_product]
  exact expect_comm _ _ _

private theorem box_shift_bound {d : ℕ} (N : Fin d → ℕ)
    (hN : ∀ j, 0 < N j) (i : Fin d) (h : ℕ) (f : (Fin d → ℕ) → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) :
    ‖(𝔼 n ∈ Fintype.piFinset (fun j => range (N j)),
        f (Function.update n i (n i + h))) -
      (𝔼 n ∈ Fintype.piFinset (fun j => range (N j)), f n)‖ ≤ 2 * h / (N i : ℝ) := by
  classical
  rw [box_average_split N i, box_average_split N i, ← expect_sub_distrib]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply Finset.expect_le
  · exact Fintype.piFinset_nonempty.mpr (fun j => nonempty_range_iff.mpr (hN j).ne')
  · intro y hy
    have heq (x : ℕ) :
        Function.update ((Equiv.funSplitAt i ℕ).symm (x, y)) i
          (((Equiv.funSplitAt i ℕ).symm (x, y)) i + h) =
        (Equiv.funSplitAt i ℕ).symm (x + h, y) := by
      ext j
      by_cases hj : j = i
      · subst j; simp [Equiv.funSplitAt_symm_apply]
      · simp [Equiv.funSplitAt_symm_apply, hj]
    simp_rw [heq]
    exact shifted_interval_average_bound (fun x => f ((Equiv.funSplitAt i ℕ).symm (x, y)))
      (fun x => hf _) (N i) h

private theorem box_coordinate_tendsto {d : ℕ} (i : Fin d) :
    Tendsto (fun N : Fin d → ℕ => N i) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  exact eventually_atTop.mpr ⟨fun _ => b, fun N hN => hN i⟩

private theorem box_shift_tendsto {d : ℕ} (i : Fin d) (h : ℕ)
    (f : (Fin d → ℕ) → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) :
    Tendsto (fun N : Fin d → ℕ =>
      (𝔼 n ∈ Fintype.piFinset (fun j => range (N j)),
        f (Function.update n i (n i + h))) -
      (𝔼 n ∈ Fintype.piFinset (fun j => range (N j)), f n)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _
    ((tendsto_const_div_atTop_nhds_zero_nat (2 * h : ℝ)).comp (box_coordinate_tendsto i))
  filter_upwards [eventually_ge_atTop (fun _ : Fin d => 1)] with N hN
  exact box_shift_bound N (fun j => hN j) i h f hf

private theorem rectangular_van_der_corput {d : ℕ} (i : Fin d)
    (f : (Fin d → ℕ) → ℂ) (hf : ∀ n, ‖f n‖ = 1)
    (hcorr : ∀ h k : ℕ, h ≠ k →
      Tendsto (fun N : Fin d → ℕ =>
        𝔼 n ∈ Fintype.piFinset (fun j => range (N j)),
          f (Function.update n i (n i + h)) * star (f (Function.update n i (n i + k))))
        atTop (𝓝 0)) :
    Tendsto (fun N : Fin d → ℕ =>
      𝔼 n ∈ Fintype.piFinset (fun j => range (N j)), f n) atTop (𝓝 0) := by
  apply cancellation_of_correlations atTop
    (fun N : Fin d → ℕ => Fintype.piFinset (fun j => range (N j))) f
    (fun n h => f (Function.update n i (n i + h)))
  · filter_upwards [eventually_ge_atTop (fun _ : Fin d => 1)] with N hN
    exact Fintype.piFinset_nonempty.mpr (fun j => nonempty_range_iff.mpr (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (hN j))))
  · exact fun n h => hf _
  · exact fun h => box_shift_tendsto i h f (fun n => (hf n).le)
  · exact hcorr

end D5.S1.Phase.MultivariateWeylRectangles
