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
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Topology.UniformSpace.Equicontinuity
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.Indexes
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UrysohnsLemma

noncomputable section

namespace D5.S1.Phase.MultivariateWeylRectangles

open Filter Finset
open scoped Topology BigOperators

/-- The phase of an integer polynomial evaluated at one natural-number tuple. -/
def polynomialPhase {d : ℕ} (α : ℝ) (Q : MvPolynomial (Fin d) ℤ)
    (n : Fin d → ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * α *
    (MvPolynomial.eval (fun i => (n i : ℤ)) Q : ℂ))

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
  have hg := (hgap.norm).eventually (gt_mem_nhds
    (show ‖(0 : ℂ)‖ < ε / 2 by simpa only [norm_zero] using half_pos hε))
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

local notation:max "coordinateTranslation" i:arg h:arg =>
  (MvPolynomial.aeval (fun j : Fin d => X j + C (ite (j = i) h 0)) :
    MvPolynomial (Fin d) ℤ →ₐ[ℤ] MvPolynomial (Fin d) ℤ)

private theorem low_mono {p : MvPolynomial (Fin d) ℤ} {m n : ℕ}
    (h : p ∈ low m) (hmn : m ≤ n) : p ∈ low n :=
  MvPolynomial.restrictSupport_mono ℤ (fun _ hv => lt_of_lt_of_le hv hmn) h

private theorem low_zero {p : MvPolynomial (Fin d) ℤ} (h : p ∈ low 0) : p = 0 := by
  apply MvPolynomial.support_eq_empty.mp
  exact Finset.eq_empty_iff_forall_notMem.mpr fun v hv => Nat.not_lt_zero _ (h hv)

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
      simpa only [aeval_C, algebraMap_eq, monomial_zero'] using hc
    · simp
  have hstep (p : MvPolynomial (Fin d) ℤ) (n : ℕ) (j : Fin d)
      (hp : coordinateTranslation i h p ∈ low (n + 1) ∧
        coordinateTranslation i h p - p ∈ low n ∧
        coordinateTranslation i h p - p - C h * pderiv i p ∈ low (n - 1)) :
      coordinateTranslation i h (p * X j) ∈ low (n + 1 + 1) ∧
      coordinateTranslation i h (p * X j) - p * X j ∈ low (n + 1) ∧
      coordinateTranslation i h (p * X j) - p * X j - C h * pderiv i (p * X j)
        ∈ low n := by
    have hx : coordinateTranslation i h (X j) = X j + C (if j = i then h else 0) := by
      simp
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
        ∑ v ∈ Q.support, coordinateTranslation i h (monomial v (Q.coeff v)) := by
      rw [← map_sum, ← Q.as_sum]
    rw [he]
    exact (low (Q.totalDegree + 1)).sum_mem (fun v hv' =>
      low_mono (translation_jet_monomial i h v (Q.coeff v)).1 (Nat.add_le_add_right (hv v hv') 1))
  constructor
  · have he : coordinateTranslation i h Q - Q =
        ∑ v ∈ Q.support, (coordinateTranslation i h (monomial v (Q.coeff v)) - monomial v (Q.coeff v)) := by
      rw [sum_sub_distrib, ← map_sum, ← Q.as_sum]
    rw [he]
    exact (low Q.totalDegree).sum_mem (fun v hv' =>
      low_mono (translation_jet_monomial i h v (Q.coeff v)).2.1 (hv v hv'))
  · have he : coordinateTranslation i h Q - Q - C h * pderiv i Q =
        ∑ v ∈ Q.support, (coordinateTranslation i h (monomial v (Q.coeff v)) - monomial v (Q.coeff v) -
          C h * pderiv i (monomial v (Q.coeff v))) := by
      simp only [sum_sub_distrib, ← mul_sum, ← map_sum, ← Q.as_sum]
    rw [he]
    exact (low (Q.totalDegree - 1)).sum_mem (fun v hv' =>
      low_mono (translation_jet_monomial i h v (Q.coeff v)).2.2 (Nat.sub_le_sub_right (hv v hv') 1))

private theorem low_homogeneous_zero {p : MvPolynomial (Fin d) ℤ} {n : ℕ}
    (hp : p ∈ low n) : homogeneousComponent n p = 0 := by
  exact homogeneousComponent_eq_zero' n p (fun v hv => ne_of_lt (hp hv))

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
    have hc := congrArg (fun p => AddMonoidAlgebra.coeff p v) hz
    rw [coeff_homogeneousComponent, if_pos hvdeg, MvPolynomial.coeff_zero] at hc
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
    · intro a; simp
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
  have hdec : Q = C (Q.coeff 0) + homogeneousComponent 1 Q := by
    have hs := sum_homogeneousComponent Q
    simpa [hD, sum_range_succ, homogeneousComponent_zero] using hs.symm
  have hp : pderiv i Q = pderiv i (homogeneousComponent 1 Q) := by
    conv_lhs => rw [hdec, map_add, pderiv_C, zero_add]
  have hpd : (pderiv i Q).totalDegree = 0 := by
    rw [hp]
    exact Nat.eq_zero_of_le_zero (by
      simpa using (homogeneousComponent_isHomogeneous 1 Q).pderiv.totalDegree_le)
  let a : ℤ := (pderiv i Q).coeff 0
  have haeq : pderiv i Q = C a := totalDegree_eq_zero_iff_eq_C.mp hpd
  have ha : a ≠ 0 := by
    intro hz
    apply hi
    rw [hD, ← hp, haeq, hz, map_zero]
  have hev (y : {j : Fin d // j ≠ i} → ℕ) (x : ℕ) :
      eval (fun j => (((Equiv.funSplitAt i ℕ).symm (x, y)) j : ℤ)) Q =
      eval (fun j => (((Equiv.funSplitAt i ℕ).symm (0, y)) j : ℤ)) Q + (x : ℤ) * a := by
    have hj := low_zero (by simpa only [hD, Nat.sub_self] using (translation_jet i (x : ℤ) Q).2.2)
    have he := congrArg (eval (fun j => (((Equiv.funSplitAt i ℕ).symm (0, y)) j : ℤ))) hj
    rw [map_sub, map_sub, map_mul, eval_C, haeq, eval_C, map_zero,
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
private theorem polynomial_rectangular_tendsto (α : ℝ) (hα : Irrational α)
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
    ∀ ε : ℝ, 0 < ε → ∃ R : ℕ, 1 ≤ R ∧ ∀ N : Fin d → ℕ,
      (∀ i, R ≤ N i) →
      ‖𝔼 n ∈ Fintype.piFinset (fun i => range (N i)), polynomialPhase α Q n‖ < ε := by
  intro ε hε
  have ht := Metric.tendsto_nhds.mp (polynomial_rectangular_tendsto α hα Q hQ) ε hε
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ht
  refine ⟨max 1 (univ.sup N₀), le_max_left _ _, fun N hN => ?_⟩
  simpa only [dist_zero_right] using hN₀ N (fun i =>
    (le_sup (f := N₀) (mem_univ i)).trans ((le_max_right 1 _).trans (hN i)))


end PolynomialDifference

section ContinuousObservables

open MeasureTheory

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {κ : Type*} [Fintype κ]

private theorem integral_character (k : κ → ℤ) :
    (∫ x : UnitAddTorus κ, UnitAddTorus.mFourier k x) = if k = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := κ))) 0 k
  simpa only [ContinuousMap.inner_toLp, ← UnitAddTorus.mFourier_neg,
    ← UnitAddTorus.mFourier_add, neg_zero, add_zero, eq_comm] using h

private theorem continuous_of_characters {ι β : Type*} (l : Filter β)
    (s : β → Finset ι) (x : ι → UnitAddTorus κ)
    (hne : ∀ᶠ b in l, (s b).Nonempty)
    (hchar : ∀ k : κ → ℤ, k ≠ 0 →
      Tendsto (fun b => 𝔼 n ∈ s b, UnitAddTorus.mFourier k (x n)) l (𝓝 0))
    (F : C(UnitAddTorus κ, ℂ)) :
    Tendsto (fun b => 𝔼 n ∈ s b, F (x n)) l (𝓝 (∫ z, F z)) := by
  classical
  let A (b : β) : C(UnitAddTorus κ, ℂ) →L[ℂ] ℂ :=
    ((s b).card : ℂ)⁻¹ • ∑ n ∈ s b, ContinuousMap.evalCLM ℂ (x n)
  have hA (b : β) (f : C(UnitAddTorus κ, ℂ)) : A b f = 𝔼 n ∈ s b, f (x n) := by
    simp [A, expect_eq_sum_div_card, div_eq_mul_inv, mul_comm]
  have hbound (b : β) (f : C(UnitAddTorus κ, ℂ)) : ‖A b f‖ ≤ ‖f‖ := by
    rw [hA]
    rcases (s b).eq_empty_or_nonempty with hb | hb
    · simp [hb]
    exact (RCLike.norm_expect_le (K := ℂ)).trans
      (expect_le hb (fun n _ => f.norm_coe_le_norm (x n)))
  let J : C(UnitAddTorus κ, ℂ) →L[ℂ] ℂ :=
    (L1.integralCLM' ℂ).comp (ContinuousMap.toLp 1 volume ℂ)
  have hJ (f : C(UnitAddTorus κ, ℂ)) : J f = ∫ z, f z := by
    change L1.integralCLM' ℂ (ContinuousMap.toLp 1 volume ℂ f) = _
    rw [← L1.integral_eq' ℂ, L1.integral_eq_integral]
    exact integral_congr_ae (ContinuousMap.coeFn_toLp volume f)
  let S : Submodule ℂ C(UnitAddTorus κ, ℂ) :=
    { carrier := {f | Tendsto (fun b => A b f) l (𝓝 (J f))}
      zero_mem' := by simpa using (tendsto_const_nhds (x := (0 : ℂ)) : Tendsto (fun _ : β => (0 : ℂ)) l (𝓝 0))
      add_mem' := by intro f g hf hg; simpa only [Set.mem_ofPred_eq, map_add] using hf.add hg
      smul_mem' := by
        intro c f hf
        simpa only [Set.mem_ofPred_eq, map_smul] using hf.const_smul c }
  have hclosed : IsClosed (S : Set C(UnitAddTorus κ, ℂ)) := by
    apply Equicontinuous.isClosed_setOfPred_tendsto _ J.continuous
    apply (LipschitzWith.uniformEquicontinuous _ 1 _).equicontinuous
    intro b
    apply LipschitzWith.of_dist_le_mul
    intro f g
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub] using hbound b (f - g)
  have hspan : Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := κ))) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    change Tendsto _ _ _
    simp only [hA, hJ, integral_character]
    split_ifs with hk
    · subst k
      simp only [UnitAddTorus.mFourier_zero, ContinuousMap.one_apply]
      exact tendsto_const_nhds.congr' (hne.mono fun b hb => (expect_const hb 1).symm)
    · exact hchar k hk
  have htop : (⊤ : Submodule ℂ C(UnitAddTorus κ, ℂ)) ≤ S := by
    rw [← UnitAddTorus.span_mFourier_closure_eq_top]
    exact Submodule.topologicalClosure_minimal _ hspan hclosed
  have hF : Tendsto (fun b => A b F) l (𝓝 (J F)) := htop (Submodule.mem_top (x := F))
  simpa only [hA, hJ] using hF

private theorem shifted_polynomial (Q : MvPolynomial (Fin d) ℤ)
    (a : Fin d → ℤ) (hQ : 0 < Q.totalDegree) :
    0 < (MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (a i)) Q).totalDegree := by
  let T (a : Fin d → ℤ) : MvPolynomial (Fin d) ℤ →ₐ[ℤ] MvPolynomial (Fin d) ℤ :=
    MvPolynomial.aeval
    (fun i => MvPolynomial.X i + MvPolynomial.C (a i))
  have hinv : (T (-a)).comp (T a) = AlgHom.id ℤ (MvPolynomial (Fin d) ℤ) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [T]
  by_contra hn
  have hC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_not_pos hn)
  have he := congrArg (T (-a)) hC
  change T (-a) (T a Q) = _ at he
  rw [← AlgHom.comp_apply, hinv] at he
  have hc : Q = MvPolynomial.C
      (AddMonoidAlgebra.coeff (T a Q) 0) := by simpa [T] using he
  rw [hc, MvPolynomial.totalDegree_C] at hQ
  omega

/-- Distinct nonconstant integer monomials, evaluated after a fixed nonnegative shift. -/
def monomialOrbit {d : ℕ} (α : ℝ) (e : κ → (Fin d →₀ ℕ))
    (a n : Fin d → ℕ) : UnitAddTorus κ :=
  fun j => ((α * (MvPolynomial.eval (fun i => ((n i + a i : ℕ) : ℤ))
    (MvPolynomial.monomial (e j) 1) : ℝ)) : UnitAddCircle)

private theorem character_monomialOrbit {d : ℕ} (α : ℝ)
    (e : κ → (Fin d →₀ ℕ)) (a n : Fin d → ℕ) (k : κ → ℤ) :
    UnitAddTorus.mFourier k (monomialOrbit α e a n) =
      polynomialPhase α
        (MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (a i : ℤ))
          (∑ j, MvPolynomial.monomial (e j) (k j))) n := by
  classical
  have he (Q : MvPolynomial (Fin d) ℤ) :
      MvPolynomial.eval (fun i => (n i : ℤ))
        (MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (a i : ℤ)) Q) =
      MvPolynomial.eval (fun i => ((n i + a i : ℕ) : ℤ)) Q := by
    apply MvPolynomial.induction_on Q
    · intro c; simp
    · intro p q hp hq; simp only [map_add, hp, hq]
    · intro p i hp
      simp only [map_mul, hp, MvPolynomial.aeval_X, map_add,
        MvPolynomial.eval_X, MvPolynomial.eval_C, Nat.cast_add]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, monomialOrbit, fourier_coe_apply,
    polynomialPhase, he]
  rw [← Complex.exp_sum]
  congr 1
  simp only [map_sum, MvPolynomial.eval_monomial]
  push_cast
  simp only [one_mul, div_one, Finset.mul_sum]
  apply sum_congr rfl
  intro j _
  simp only [Finsupp.prod]
  push_cast
  ring

/-- Every continuous complex observable has its Haar average along unrestricted
rectangles of any finite family of distinct nonconstant monomials, with any fixed shift. -/
theorem monomial_rectangular_equidistribution {d : ℕ} (α : ℝ) (hα : Irrational α)
    (e : κ → (Fin d →₀ ℕ)) (he : Function.Injective e) (hzero : ∀ j, e j ≠ 0)
    (a : Fin d → ℕ) (F : C(UnitAddTorus κ, ℂ)) :
    Tendsto (fun N : Fin d → ℕ =>
      𝔼 n ∈ Fintype.piFinset (fun i => range (N i)), F (monomialOrbit α e a n))
      atTop (𝓝 (∫ z, F z)) := by
  classical
  apply continuous_of_characters
  · filter_upwards [eventually_ge_atTop (fun _ : Fin d => 1)] with N hN
    exact Fintype.piFinset_nonempty.mpr (fun i =>
      nonempty_range_iff.mpr (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (hN i))))
  intro k hk
  simp_rw [character_monomialOrbit]
  suffices hcancel : ∀ ε : ℝ, 0 < ε → ∃ R : ℕ, 1 ≤ R ∧ ∀ N : Fin d → ℕ,
      (∀ i, R ≤ N i) → ‖𝔼 n ∈ Fintype.piFinset (fun i => range (N i)),
        polynomialPhase α (MvPolynomial.aeval
          (fun i => MvPolynomial.X i + MvPolynomial.C (a i : ℤ))
          (∑ j, MvPolynomial.monomial (e j) (k j))) n‖ < ε by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨R, _, hR⟩ := hcancel ε hε
    filter_upwards [eventually_ge_atTop (fun _ : Fin d => R)] with N hN
    simpa only [dist_zero_right] using hR N hN
  apply polynomial_rectangular_cancellation α hα
  apply shifted_polynomial
  by_contra hn
  have hC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_not_pos hn)
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hk
  have hc := congrArg (fun p => AddMonoidAlgebra.coeff p (e j)) hC
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial] at hc
  have hcoeff : (∑ i : κ, if e i = e j then k i else 0) = k j := by
    simp [he.eq_iff]
  rw [hcoeff, MvPolynomial.coeff_C_of_ne_zero (hzero j)] at hc
  exact hj hc

private theorem one_dimensional_average (N : ℕ) (f : (Fin 1 → ℕ) → ℂ) :
    (𝔼 n ∈ Fintype.piFinset (fun _ : Fin 1 => range N), f n) =
      𝔼 t ∈ range N, f (fun _ => t) := by
  apply expect_equiv (Equiv.funUnique (Fin 1) ℕ)
  · intro n
    simp only [Fintype.mem_piFinset, Equiv.funUnique_apply]
    exact ⟨fun h => h default, fun h i => by simpa only [Subsingleton.elim i default] using h⟩
  · intro n _
    congr 1
    funext i
    exact congrArg n (Subsingleton.elim i 0)

/-- Along the common curve n(i) = t^(B^i), sampling begins at t = 1. -/
theorem monomial_curve_equidistribution {d : ℕ} (α : ℝ) (hα : Irrational α)
    (e : κ → (Fin d →₀ ℕ)) (he : Function.Injective e) (hzero : ∀ j, e j ≠ 0)
    (B : ℕ) (hB : 2 ≤ B) (hdigit : ∀ j i, e j i < B)
    (F : C(UnitAddTorus κ, ℂ)) :
    Tendsto (fun L : ℕ => 𝔼 t ∈ range L,
      F (monomialOrbit α e 0 (fun i => (t + 1) ^ (B ^ i.val))))
      atTop (𝓝 (∫ z, F z)) := by
  classical
  let c (j : κ) := Nat.ofDigits B (List.ofFn (e j))
  have hc (j : κ) : c j = ∑ i : Fin d, e j i * B ^ i.val := by
    simp [c, Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.sum_ofFn]
  have hinj : Function.Injective c := by
    intro j k hjk
    apply he
    apply Finsupp.ext
    exact congrFun (List.ofFn_inj.mp (Nat.ofDigits_inj_of_len_eq (by omega)
      (by simp) (by simpa using hdigit j) (by simpa using hdigit k) hjk))
  have hpos (j : κ) : c j ≠ 0 := by
    intro hz
    apply hzero j
    ext i
    have hi : e j i * B ^ i.val = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp ((hc j).symm.trans hz)
        i (mem_univ i)
    exact (mul_eq_zero.mp hi).resolve_right (pow_ne_zero _ (by omega))
  let e' (j : κ) : Fin 1 →₀ ℕ := Finsupp.single 0 (c j)
  have horbit (t : ℕ) : monomialOrbit α e' (fun _ => 1) (fun _ => t) =
      monomialOrbit α e 0 (fun i => (t + 1) ^ (B ^ i.val)) := by
    ext j
    apply congrArg (fun x : ℝ => (x : UnitAddCircle))
    congr 1
    simp only [MvPolynomial.eval_monomial, one_mul]
    simp only [e', Finsupp.prod_single_index, pow_zero]
    rw [Finsupp.prod_pow, hc]
    push_cast
    rw [← Finset.prod_pow_eq_pow_sum]
    apply prod_congr rfl
    intro i _
    simp only [Pi.zero_apply, Nat.cast_zero, add_zero, ← pow_mul, mul_comm]
  have h := monomial_rectangular_equidistribution α hα e'
    (fun j k h => hinj (Finsupp.single_injective 0 h))
    (fun j => Finsupp.single_ne_zero.mpr (hpos j))
    (fun _ => 1) F
  have ht : Tendsto (fun L : ℕ => (fun _ : Fin 1 => L)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro N
    exact (eventually_ge_atTop (N 0)).mono fun L hL i =>
      by simpa only [Subsingleton.elim i 0] using hL
  have hh := h.comp ht
  simpa only [Function.comp_def, one_dimensional_average, horbit] using hh

/-- Every nonempty open set is attained arbitrarily far out along the same curve,
with every input coordinate above the prescribed threshold. -/
theorem monomial_curve_visits {d : ℕ} (hd : 0 < d) (α : ℝ) (hα : Irrational α)
    (e : κ → (Fin d →₀ ℕ)) (he : Function.Injective e) (hzero : ∀ j, e j ≠ 0)
    (hinput : ∀ i : Fin d, ∃ j, e j = Finsupp.single i 1)
    (B : ℕ) (hdigit : ∀ j i, e j i < B)
    (U : Set (UnitAddTorus κ)) (hU : IsOpen U) (hUne : U.Nonempty) (T : ℕ) :
    ∃ t : ℕ, max T 1 ≤ t ∧
      monomialOrbit α e 0 (fun i => t ^ (B ^ i.val)) ∈ U ∧
      ∀ i : Fin d, T ≤ t ^ (B ^ i.val) := by
  classical
  have hB : 2 ≤ B := by
    obtain ⟨j, hj⟩ := hinput ⟨0, hd⟩
    have hb := hdigit j ⟨0, hd⟩
    simp only [hj, Finsupp.single_eq_same] at hb
    omega
  suffices hv : ∃ t : ℕ, max T 1 ≤ t ∧
      monomialOrbit α e 0 (fun i => t ^ (B ^ i.val)) ∈ U by
    obtain ⟨t, ht, hu⟩ := hv
    exact ⟨t, ht, hu, fun i => (le_max_left T 1).trans (ht.trans
      (le_self_pow ((le_max_right T 1).trans ht) (pow_ne_zero _ (by omega))))⟩
  by_contra hn
  push Not at hn
  obtain ⟨y, hy⟩ := hUne
  obtain ⟨f, hf1, hfc, hfs, hf01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen isCompact_singleton hU
      (Set.singleton_subset_iff.mpr hy)
  have hpos : 0 < ∫ z, f z := integral_pos_of_integrable_nonneg_nonzero (x := y)
    f.continuous (f.continuous.integrable_of_hasCompactSupport hfc)
    (fun z => (hf01 z).1) (by simpa only [hf1 (Set.mem_singleton y), Pi.one_apply] using (one_ne_zero : (1 : ℝ) ≠ 0))
  let F : C(UnitAddTorus κ, ℂ) := ⟨fun z => (f z : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hzeroTail : ∀ᶠ t : ℕ in atTop,
      F (monomialOrbit α e 0 (fun i => (t + 1) ^ (B ^ i.val))) = 0 := by
    filter_upwards [eventually_ge_atTop (max T 1)] with t ht
    have hout := hn (t + 1) (by omega)
    have hz : f (monomialOrbit α e 0 (fun i => (t + 1) ^ (B ^ i.val))) = 0 := by
      by_contra hz
      exact hout (hfs (subset_closure hz))
    simp only [F, ContinuousMap.coe_mk, hz, Complex.ofReal_zero]
  have hseq : Tendsto (fun t : ℕ =>
      F (monomialOrbit α e 0 (fun i => (t + 1) ^ (B ^ i.val)))) atTop (𝓝 (0 : ℂ)) :=
    tendsto_const_nhds.congr' (hzeroTail.mono fun _ h => h.symm)
  have hlim0 := hseq.cesaro_smul
  have hlim := monomial_curve_equidistribution α hα e he hzero B hB hdigit F
  have hlim0' : Tendsto (fun L : ℕ => 𝔼 t ∈ range L,
      F (monomialOrbit α e 0 (fun i => (t + 1) ^ (B ^ i.val)))) atTop (𝓝 0) := by
    simpa only [expect_eq_sum_div_card, card_range, Complex.real_smul,
      Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv, mul_comm] using hlim0
  have heq := tendsto_nhds_unique hlim hlim0'
  change (∫ z, (f z : ℂ)) = 0 at heq
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at heq
  exact hpos.ne' heq

end ContinuousObservables

end D5.S1.Phase.MultivariateWeylRectangles
