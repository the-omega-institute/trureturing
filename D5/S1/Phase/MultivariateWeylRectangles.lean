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
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Basic

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

section PolynomialDifference

open MvPolynomial
variable {d : ℕ}

local notation:max "low" n:arg =>
  (MvPolynomial.restrictSupport ℤ (Set.ofPred (fun v : Fin d →₀ ℕ => Finsupp.degree v < n)))

/-- Translation in one coordinate as an algebra endomorphism. -/
def coordinateTranslation (i : Fin d) (h : ℤ) :
    MvPolynomial (Fin d) ℤ →ₐ[ℤ] MvPolynomial (Fin d) ℤ :=
  MvPolynomial.aeval (fun j => X j + C (if j = i then h else 0))

private theorem low_mono {p : MvPolynomial (Fin d) ℤ} {m n : ℕ}
    (h : p ∈ low m) (hmn : m ≤ n) : p ∈ low n :=
  MvPolynomial.restrictSupport_mono ℤ (fun _ hv => lt_of_lt_of_le hv hmn) h

private theorem low_zero {p : MvPolynomial (Fin d) ℤ} (h : p ∈ low 0) : p = 0 := by
  apply MvPolynomial.ext
  intro v
  by_contra hv
  have hmem : v ∈ p.support := mem_support_iff.mpr (by simpa using hv)
  exact Nat.not_lt_zero _ (h hmem)

private theorem low_mul_X {p : MvPolynomial (Fin d) ℤ} {n : ℕ}
    (h : p ∈ low n) (j : Fin d) : p * X j ∈ low (n + 1) := by
  intro v hv
  change v ∈ (p * X j).support at hv
  change v.degree < n + 1
  rw [support_mul_X] at hv
  rcases mem_map.mp hv with ⟨u, hu, rfl⟩
  simpa using Nat.add_lt_add_right (h hu) 1

private theorem low_C_mul {p : MvPolynomial (Fin d) ℤ} {n : ℕ}
    (h : p ∈ low n) (c : ℤ) : C c * p ∈ low n := by
  simpa only [C_mul'] using (low n).smul_mem c h

private theorem translation_jet_monomial (i : Fin d) (h : ℤ)
    (v : Fin d →₀ ℕ) (c : ℤ) :
    coordinateTranslation i h (monomial v c) ∈ low (v.degree + 1) ∧
    coordinateTranslation i h (monomial v c) - monomial v c ∈ low v.degree ∧
    coordinateTranslation i h (monomial v c) - monomial v c -
      C h * pderiv i (monomial v c) ∈ low (v.degree - 1) := by
  have hC (a : ℤ) :
      coordinateTranslation i h (C a) ∈ low 1 ∧
      coordinateTranslation i h (C a) - C a ∈ low 0 ∧
      coordinateTranslation i h (C a) - C a - C h * pderiv i (C a) ∈ low 0 := by
    constructor
    · have hc : monomial (0 : Fin d →₀ ℕ) a ∈ low 1 :=
        (monomial_mem_restrictSupport (R := ℤ)).mpr (Or.inl (by change Finsupp.degree (0 : Fin d →₀ ℕ) < 1; simp))
      simpa only [coordinateTranslation, aeval_C, algebraMap_eq, monomial_zero'] using hc
    · simp [coordinateTranslation]
  have hstep (p : MvPolynomial (Fin d) ℤ) (n : ℕ) (j : Fin d)
      (hp : coordinateTranslation i h p ∈ low (n + 1) ∧
        coordinateTranslation i h p - p ∈ low n ∧
        coordinateTranslation i h p - p - C h * pderiv i p ∈ low (n - 1)) :
      coordinateTranslation i h (p * X j) ∈ low (n + 1 + 1) ∧
      coordinateTranslation i h (p * X j) - p * X j ∈ low (n + 1) ∧
      coordinateTranslation i h (p * X j) - p * X j - C h * pderiv i (p * X j)
        ∈ low n := by
    have hx : coordinateTranslation i h (X j) = X j + C (if j = i then h else 0) := by
      simp [coordinateTranslation]
    rw [map_mul, hx]
    constructor
    · rw [mul_add]
      exact (low (n + 1 + 1)).add_mem (low_mul_X hp.1 j)
        (low_mono (by simpa [mul_comm] using low_C_mul hp.1 (if j = i then h else 0))
          (Nat.le_succ _))
    constructor
    · have he : coordinateTranslation i h p * (X j + C (if j = i then h else 0)) - p * X j =
          (coordinateTranslation i h p - p) * X j +
            C (if j = i then h else 0) * coordinateTranslation i h p := by ring
      rw [he]
      exact (low (n + 1)).add_mem (low_mul_X hp.2.1 j) (low_C_mul hp.1 _)
    · have he : coordinateTranslation i h p * (X j + C (if j = i then h else 0)) - p * X j -
          C h * pderiv i (p * X j) =
          (coordinateTranslation i h p - p - C h * pderiv i p) * X j +
            C (if j = i then h else 0) * (coordinateTranslation i h p - p) := by
        by_cases hj : j = i
        · subst j; simp only [pderiv_mul, pderiv_X_self, mul_one, ite_true]; simp; ring
        · simp only [pderiv_mul, pderiv_X_of_ne hj, mul_zero, add_zero, if_neg hj, map_zero]; ring
      rw [he]
      apply (low n).add_mem _ (low_C_mul hp.2.1 _)
      cases n with
      | zero => rw [low_zero hp.2.2, zero_mul]; exact (low 0).zero_mem
      | succ n => simpa using low_mul_X hp.2.2 j
  induction v using Finsupp.induction with
  | zero => simpa [monomial_zero'] using hC c
  | @single_add i' e v hi he ih =>
    have hp : ∀ e : ℕ,
        coordinateTranslation i h (monomial v c * X i' ^ e) ∈ low (v.degree + e + 1) ∧
        coordinateTranslation i h (monomial v c * X i' ^ e) - monomial v c * X i' ^ e
          ∈ low (v.degree + e) ∧
        coordinateTranslation i h (monomial v c * X i' ^ e) - monomial v c * X i' ^ e -
          C h * pderiv i (monomial v c * X i' ^ e) ∈ low (v.degree + e - 1) := by
      intro e
      induction e with
      | zero => simpa using ih
      | succ e he =>
        simpa [pow_succ, ← mul_assoc, Nat.add_assoc] using
          hstep (monomial v c * X i' ^ e) (v.degree + e) i' he
    simpa [add_comm, monomial_add_single, map_add, Finsupp.degree_single] using hp e

private theorem translation_jet (i : Fin d) (h : ℤ) (Q : MvPolynomial (Fin d) ℤ) :
    coordinateTranslation i h Q ∈ low (Q.totalDegree + 1) ∧
    coordinateTranslation i h Q - Q ∈ low Q.totalDegree ∧
    coordinateTranslation i h Q - Q - C h * pderiv i Q ∈ low (Q.totalDegree - 1) := by
  have hv (v : Fin d →₀ ℕ) (hv : v ∈ Q.support) : v.degree ≤ Q.totalDegree :=
    le_totalDegree hv
  constructor
  · have he : coordinateTranslation i h Q =
        ∑ v ∈ Q.support, coordinateTranslation i h (monomial v (coeff v Q)) := by
      rw [← map_sum, ← Q.as_sum]
    rw [he]
    exact (low (Q.totalDegree + 1)).sum_mem (fun v hv' =>
      low_mono (translation_jet_monomial i h v (coeff v Q)).1 (Nat.add_le_add_right (hv v hv') 1))
  constructor
  · have he : coordinateTranslation i h Q - Q =
        ∑ v ∈ Q.support, (coordinateTranslation i h (monomial v (coeff v Q)) - monomial v (coeff v Q)) := by
      rw [sum_sub_distrib, ← map_sum, ← Q.as_sum]
    rw [he]
    exact (low Q.totalDegree).sum_mem (fun v hv' =>
      low_mono (translation_jet_monomial i h v (coeff v Q)).2.1 (hv v hv'))
  · have he : coordinateTranslation i h Q - Q - C h * pderiv i Q =
        ∑ v ∈ Q.support, (coordinateTranslation i h (monomial v (coeff v Q)) - monomial v (coeff v Q) -
          C h * pderiv i (monomial v (coeff v Q))) := by
      simp only [sum_sub_distrib, ← mul_sum, ← map_sum, ← Q.as_sum]
    rw [he]
    exact (low (Q.totalDegree - 1)).sum_mem (fun v hv' =>
      low_mono (translation_jet_monomial i h v (coeff v Q)).2.2 (Nat.sub_le_sub_right (hv v hv') 1))

private theorem low_homogeneous_zero {p : MvPolynomial (Fin d) ℤ} {n : ℕ}
    (hp : p ∈ low n) : homogeneousComponent n p = 0 := by
  apply MvPolynomial.ext
  intro v
  rw [coeff_homogeneousComponent, coeff_zero]
  split_ifs with hv
  · by_contra hc
    have hd : v.degree < n := hp (mem_support_iff.mpr hc)
    omega
  · rfl

private theorem homogeneous_pderiv (Q : MvPolynomial (Fin d) ℤ) (i : Fin d) (n : ℕ) :
    homogeneousComponent n (pderiv i Q) = pderiv i (homogeneousComponent (n + 1) Q) := by
  apply MvPolynomial.ext
  intro v
  simp only [coeff_homogeneousComponent, coeff_pderiv, map_add,
    Finsupp.degree_single, Nat.add_right_cancel_iff]
  split_ifs <;> simp_all

private theorem difference_top (i : Fin d) (h k : ℤ) (Q : MvPolynomial (Fin d) ℤ) :
    homogeneousComponent (Q.totalDegree - 1)
      (coordinateTranslation i k Q - coordinateTranslation i h Q) =
    C (k - h) * homogeneousComponent (Q.totalDegree - 1) (pderiv i Q) := by
  have hk := low_homogeneous_zero (translation_jet i k Q).2.2
  have hh := low_homogeneous_zero (translation_jet i h Q).2.2
  simp only [map_sub, homogeneousComponent_C_mul] at hk hh ⊢
  linear_combination hk - hh

private theorem low_totalDegree_lt {p : MvPolynomial (Fin d) ℤ} {n : ℕ}
    (hn : 0 < n) (hp : p ∈ low n) : p.totalDegree < n := by
  rw [totalDegree, Finset.sup_lt_iff hn]
  exact fun v hv => hp hv

private theorem exists_top_coordinate (Q : MvPolynomial (Fin d) ℤ) (hD : 0 < Q.totalDegree) :
    ∃ i : Fin d, pderiv i (homogeneousComponent Q.totalDegree Q) ≠ 0 := by
  classical
  have hQ : Q ≠ 0 := by intro h; simp [h] at hD
  have htop : homogeneousComponent Q.totalDegree Q ≠ 0 := by
    obtain ⟨v, hv, hmax⟩ := Q.support.exists_mem_eq_sup (support_nonempty.mpr hQ)
      (fun v : Fin d →₀ ℕ => v.degree)
    have hvdeg : v.degree = Q.totalDegree := hmax.symm
    intro hz
    have hc := congrArg (coeff v) hz
    rw [coeff_homogeneousComponent, if_pos hvdeg, coeff_zero] at hc
    exact mem_support_iff.mp hv hc
  by_contra! hall
  have he := (homogeneousComponent_isHomogeneous Q.totalDegree Q).sum_X_mul_pderiv
  simp only [hall, mul_zero, sum_const_zero, nsmul_eq_mul] at he
  exact (mul_ne_zero (Nat.cast_ne_zero.mpr hD.ne') htop) he.symm

private theorem coordinate_difference_degree (Q : MvPolynomial (Fin d) ℤ)
    (hD : 2 ≤ Q.totalDegree) (i : Fin d)
    (hi : pderiv i (homogeneousComponent Q.totalDegree Q) ≠ 0)
    (h k : ℤ) (hhk : h ≠ k) :
    (coordinateTranslation i k Q - coordinateTranslation i h Q).totalDegree = Q.totalDegree - 1 := by
  have hlow : coordinateTranslation i k Q - coordinateTranslation i h Q ∈ low Q.totalDegree := by
    convert (low Q.totalDegree).sub_mem (translation_jet i k Q).2.1
      (translation_jet i h Q).2.1 using 1 <;> ring
  have hu := low_totalDegree_lt (by omega : 0 < Q.totalDegree) hlow
  have ht : homogeneousComponent (Q.totalDegree - 1)
      (coordinateTranslation i k Q - coordinateTranslation i h Q) ≠ 0 := by
    rw [difference_top, homogeneous_pderiv, Nat.sub_add_cancel (by omega : 1 ≤ Q.totalDegree)]
    exact mul_ne_zero (C_ne_zero.mpr (sub_ne_zero.mpr hhk.symm)) hi
  have hl : Q.totalDegree - 1 ≤
      (coordinateTranslation i k Q - coordinateTranslation i h Q).totalDegree := by
    by_contra hn
    exact ht (homogeneousComponent_eq_zero _ _ (by omega))
  omega

private theorem eval_coordinateTranslation (Q : MvPolynomial (Fin d) ℤ)
    (i : Fin d) (h : ℤ) (n : Fin d → ℤ) :
    eval n (coordinateTranslation i h Q) = eval (Function.update n i (n i + h)) Q := by
  classical
  have he : (eval n).comp (coordinateTranslation i h).toRingHom =
      eval (Function.update n i (n i + h)) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [coordinateTranslation, MvPolynomial.algebraMap_eq]
    intro j
    change eval n (MvPolynomial.aeval (fun j => X j + C (if j = i then h else 0)) (X j)) =
      eval (Function.update n i (n i + h)) (X j)
    rw [aeval_X, map_add, eval_X, eval_C, eval_X]
    by_cases hj : j = i
    · subst j; simp
    · simp [hj]
  exact DFunLike.congr_fun he Q

private theorem phase_norm (α : ℝ) (Q : MvPolynomial (Fin d) ℤ) (n : Fin d → ℕ) :
    ‖polynomialPhase α Q n‖ = 1 := by
  simp [polynomialPhase, Complex.norm_exp]

private theorem phase_correlation (α : ℝ) (Q : MvPolynomial (Fin d) ℤ)
    (i : Fin d) (h k : ℕ) (n : Fin d → ℕ) :
    polynomialPhase α Q (Function.update n i (n i + h)) *
      star (polynomialPhase α Q (Function.update n i (n i + k))) =
    polynomialPhase α (coordinateTranslation i (h : ℤ) Q - coordinateTranslation i (k : ℤ) Q) n := by
  have he (u : ℕ) : eval (fun j => (n j : ℤ)) (coordinateTranslation i (u : ℤ) Q) =
      eval (fun j => (Function.update n i (n i + u) j : ℤ)) Q := by
    rw [eval_coordinateTranslation]
    apply congrArg (fun v => eval v Q)
    funext j
    by_cases hj : j = i <;> simp [hj]
  simp only [polynomialPhase, map_sub, he, Int.cast_sub, Complex.star_def, ← Complex.exp_conj,
    map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast]
  rw [← Complex.exp_add]
  congr 1
  ring

private theorem degree_one_cancellation (α : ℝ) (hα : Irrational α)
    (Q : MvPolynomial (Fin d) ℤ) (hD : Q.totalDegree = 1) :
    Tendsto (fun N : Fin d → ℕ =>
      𝔼 n ∈ Fintype.piFinset (fun j => range (N j)), polynomialPhase α Q n) atTop (𝓝 0) := by
  classical
  obtain ⟨i, hi⟩ := exists_top_coordinate Q (by omega)
  have hdec : Q = C (coeff 0 Q) + homogeneousComponent 1 Q := by
    have hs := sum_homogeneousComponent Q
    simpa [hD, sum_range_succ, homogeneousComponent_zero] using hs.symm
  have hp : pderiv i Q = pderiv i (homogeneousComponent 1 Q) := by
    conv_lhs => rw [hdec, map_add, pderiv_C, zero_add]
  have hpd : (pderiv i Q).totalDegree = 0 := by
    rw [hp]
    exact Nat.eq_zero_of_le_zero (by
      simpa using (homogeneousComponent_isHomogeneous 1 Q).pderiv.totalDegree_le)
  let a : ℤ := coeff 0 (pderiv i Q)
  have haeq : pderiv i Q = C a := totalDegree_eq_zero_iff_eq_C.mp hpd
  have ha : a ≠ 0 := by
    intro hz
    apply hi
    rw [hD, ← hp, haeq, hz, map_zero]
  have hev (y : {j : Fin d // j ≠ i} → ℕ) (x : ℕ) :
      eval (fun j => (((Equiv.funSplitAt i ℕ).symm (x, y)) j : ℤ)) Q =
      eval (fun j => (((Equiv.funSplitAt i ℕ).symm (0, y)) j : ℤ)) Q + (x : ℤ) * a := by
    have hj := low_zero (by simpa [hD] using (translation_jet i (x : ℤ) Q).2.2)
    have he := congrArg (eval (fun j => (((Equiv.funSplitAt i ℕ).symm (0, y)) j : ℤ))) hj
    rw [map_sub, map_sub, map_mul, map_natCast, haeq, eval_C, map_zero,
      eval_coordinateTranslation] at he
    have heval : Function.update (fun j => (((Equiv.funSplitAt i ℕ).symm (0, y)) j : ℤ)) i
        ((((Equiv.funSplitAt i ℕ).symm (0, y)) i : ℤ) + (x : ℤ)) =
        (fun j => (((Equiv.funSplitAt i ℕ).symm (x, y)) j : ℤ)) := by
      funext j
      by_cases hj : j = i <;> simp [Equiv.funSplitAt_symm_apply, hj]
    rw [heval] at he
    linear_combination he
  let β : ℝ := (a : ℝ) * α
  let C₀ : ℝ := 2 / ‖Complex.exp (2 * Real.pi * Complex.I * (1 : ℤ) * (β : ℂ)) - 1‖
  have hslice (y : {j : Fin d // j ≠ i} → ℕ) (N : ℕ) :
      ‖𝔼 x ∈ range N, polynomialPhase α Q ((Equiv.funSplitAt i ℕ).symm (x, y))‖ ≤ C₀ / N := by
    let c : ℤ := eval (fun j => (((Equiv.funSplitAt i ℕ).symm (0, y)) j : ℤ)) Q
    have he (x : ℕ) : polynomialPhase α Q ((Equiv.funSplitAt i ℕ).symm (x, y)) =
        Complex.exp (2 * Real.pi * Complex.I * (1 : ℤ) *
          (((α * c : ℝ) + (x : ℝ) * β : ℝ) : ℂ)) := by
      unfold polynomialPhase
      rw [hev]
      congr 1
      dsimp [c, β]
      push_cast
      ring
    simp_rw [he]
    rw [expect_eq_sum_div_card, card_range, norm_div, Complex.norm_natCast]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    simpa only [C₀, Complex.ofReal_add, Complex.ofReal_mul] using
      CharacterAverage.norm_character_sum_le β (hα.intCast_mul ha) (α * c) 1 one_ne_zero N
  apply squeeze_zero_norm' _
    ((tendsto_const_div_atTop_nhds_zero_nat C₀).comp (box_coordinate_tendsto i))
  filter_upwards [eventually_ge_atTop (fun _ : Fin d => 1)] with N hN
  rw [box_average_split N i]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply Finset.expect_le
  · exact Fintype.piFinset_nonempty.mpr
      (fun j => nonempty_range_iff.mpr (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (hN j))))
  · exact fun y _ => hslice y (N i)

/-- Every nonconstant integer polynomial with an irrational common coefficient has
vanishing phase average as all rectangular side lengths tend independently to infinity. -/
theorem polynomial_rectangular_tendsto (α : ℝ) (hα : Irrational α)
    (Q : MvPolynomial (Fin d) ℤ) (hQ : 0 < Q.totalDegree) :
    Tendsto (fun N : Fin d → ℕ =>
      𝔼 n ∈ Fintype.piFinset (fun j => range (N j)), polynomialPhase α Q n) atTop (𝓝 0) := by
  generalize hdeg : Q.totalDegree = D at hQ
  induction D using Nat.strong_induction_on generalizing Q with
  | h D ih =>
    by_cases hD : D = 1
    · exact degree_one_cancellation α hα Q (hdeg.trans hD)
    have hD2 : 2 ≤ Q.totalDegree := by omega
    obtain ⟨i, hi⟩ := exists_top_coordinate Q (by omega)
    apply rectangular_van_der_corput i _ (phase_norm α Q)
    intro h k hhk
    simp_rw [phase_correlation]
    have hd := coordinate_difference_degree Q hD2 i hi (k : ℤ) (h : ℤ)
      (by exact_mod_cast hhk.symm)
    exact ih (Q.totalDegree - 1) (by omega)
      (coordinateTranslation i (h : ℤ) Q - coordinateTranslation i (k : ℤ) Q)
      hd (by omega)

/-- A single threshold works for every rectangle with every side above that threshold. -/
theorem polynomial_rectangular_cancellation (α : ℝ) (hα : Irrational α)
    (Q : MvPolynomial (Fin d) ℤ) (hQ : 0 < Q.totalDegree) :
    RectangularCancellation (polynomialPhase α Q) := by
  intro ε hε
  have ht := Metric.tendsto_nhds.mp (polynomial_rectangular_tendsto α hα Q hQ) ε hε
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ht
  refine ⟨max 1 (univ.sup N₀), le_max_left _ _, fun N hN => ?_⟩
  simpa only [dist_zero_right] using hN₀ N (fun i =>
    (le_sup (f := N₀) (mem_univ i)).trans ((le_max_right 1 _).trans (hN i)))


end PolynomialDifference

end D5.S1.Phase.MultivariateWeylRectangles
