/- GID: D5/S3/Zeros/Jensen/CompactSeparatedRealContinuation
   generality: G
   mirror-B: D5/B/S3/Zeros/Jensen/CompactSeparatedRealContinuation
   mirror-E: none(waiver:qualitative-polynomial-continuation)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Field.Approximation]
   utility: none
   digest: Uniform separation preserves real roots through compact connected polynomial families. -/

import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.Jensen.CompactSeparatedRealContinuation

open Polynomial Filter Topology
open scoped ComplexConjugate

-- Real roots cannot leave the real axis without an arbitrarily small distinct-root gap.
private theorem real_coefficients_conjugate_root
    (P : Polynomial ℂ) (hreal : ∀ i, (P.coeff i).im = 0)
    (z : ℂ) (hz : P.eval z = 0) : P.eval (conj z) = 0 := by
  have hmap : P.map (starRingEnd ℂ) = P := by
    ext i
    simpa only [Polynomial.coeff_map] using
      Complex.conj_eq_iff_im.mpr (hreal i)
  have he := Polynomial.eval_map_apply (p := P) (starRingEnd ℂ) z
  rw [hmap, hz, map_zero] at he
  exact he

private theorem separated_conjugate_roots_have_imaginary_gap
    (P : Polynomial ℂ) (hreal : ∀ i, (P.coeff i).im = 0)
    (d : ℝ)
    (hsep : ∀ z w : ℂ, P.eval z = 0 → P.eval w = 0 → z ≠ w → d ≤ ‖z - w‖)
    (z : ℂ) (hz : P.eval z = 0) (him : z.im ≠ 0) : d/2 ≤ |z.im| := by
  have hne : z ≠ conj z := by
    intro he
    exact him (Complex.conj_eq_iff_im.mp he.symm)
  have hs := hsep z (conj z) hz (real_coefficients_conjugate_root P hreal z hz) hne
  have hn : ‖z-conj z‖ = 2*|z.im| := by
    rw [Complex.sub_conj, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_mul]
    norm_num
  rw [hn] at hs
  linarith

private theorem root_approximation_tolerance
    (q : ℕ) (hq : 0 < q) (d R : ℝ) (hd : 0 < d) (hR : 0 < R) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      (((q : ℝ)+1)*epsilon)^((q : ℝ)⁻¹)*R < d := by
  let x := d/(2*R)
  let epsilon := x^q/((q : ℝ)+1)
  have hx : 0 < x := by dsimp [x]; positivity
  have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  have hbase : ((q : ℝ)+1)*epsilon = x^q := by
    dsimp [epsilon]
    field_simp
  have hroot : (x^q)^((q : ℝ)⁻¹) = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le,
      mul_inv_cancel₀ hqreal, Real.rpow_one]
  refine ⟨epsilon, hepsilon, ?_⟩
  rw [hbase, hroot]
  dsimp [x]
  have hhalf : d/(2*R)*R = d/2 := by field_simp
  rw [hhalf]
  linarith

private theorem eventually_close_all_coefficients
    {A : Type*} [TopologicalSpace A]
    (P : A → Polynomial ℂ) (q : ℕ)
    (hdegree : ∀ x, (P x).natDegree = q)
    (hc : ∀ i, Continuous (fun x => (P x).coeff i))
    (x : A) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ y in 𝓝 x, ∀ i, ‖(P x).coeff i - (P y).coeff i‖ < epsilon := by
  have hfinite : ∀ᶠ y in 𝓝 x, ∀ i ∈ Finset.range (q+1),
      ‖(P x).coeff i - (P y).coeff i‖ < epsilon := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have ht : Tendsto (fun y => ‖(P x).coeff i - (P y).coeff i‖) (𝓝 x) (𝓝 0) := by
      have hnorm := ((continuous_const : Continuous (fun _ : A => (P x).coeff i)).sub
        (hc i)).norm
      simpa using hnorm.continuousAt.tendsto (x := x)
    exact ht.eventually (eventually_lt_nhds hepsilon)
  filter_upwards [hfinite] with y hy i
  by_cases hi : i ≤ q
  · exact hy i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  · have hix : (P x).natDegree < i := by rw [hdegree x]; omega
    have hiy : (P y).natDegree < i := by rw [hdegree y]; omega
    simpa [Polynomial.coeff_eq_zero_of_natDegree_lt hix,
      Polynomial.coeff_eq_zero_of_natDegree_lt hiy] using hepsilon

private theorem separated_real_polynomial_family_preserves_root_reality
    {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    (P : A → Polynomial ℂ) (q : ℕ) (hq : 0 < q)
    (hmonic : ∀ x, (P x).Monic) (hdegree : ∀ x, (P x).natDegree = q)
    (hc : ∀ i, Continuous (fun x => (P x).coeff i))
    (R d : ℝ) (hR : 1 ≤ R) (hd : 0 < d)
    (hbound : ∀ x z, (P x).eval z = 0 → ‖z‖ ≤ R)
    (hreal : ∀ x i, ((P x).coeff i).im = 0)
    (hsep : ∀ x z w, (P x).eval z = 0 → (P x).eval w = 0 → z ≠ w → d ≤ ‖z - w‖)
    (x0 : A) (hstart : ∀ z, (P x0).eval z = 0 → z.im = 0) :
    ∀ x z, (P x).eval z = 0 → z.im = 0 := by
  let S : Set A := {x | ∀ z, (P x).eval z = 0 → z.im = 0}
  have hopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨epsilon, hepsilon, hsmall⟩ :=
      root_approximation_tolerance q hq (d/2) R (by positivity) (by linarith)
    filter_upwards [eventually_close_all_coefficients P q hdegree hc x epsilon hepsilon] with y hy
    intro z hz
    by_contra him
    obtain ⟨w, hw, hnear⟩ := Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt
      (f := P y) (g := P x) hepsilon hz (hmonic y) (hmonic x)
      (by rw [hdegree x, hdegree y]) hy (IsAlgClosed.splits (P x))
    have hwzero : (P x).eval w = 0 := (Polynomial.mem_roots (hmonic x).ne_zero).mp hw
    have hwreal := hx w hwzero
    have hmax : max ‖z‖ 1 ≤ R := max_le (hbound y z hz) hR
    have hnearGap : ‖z - w‖ < d/2 := by
      apply lt_of_lt_of_le hnear
      rw [hdegree y]
      exact (mul_le_mul_of_nonneg_left hmax (Real.rpow_nonneg (by positivity) _)).trans hsmall.le
    have himnorm : |z.im| ≤ ‖z - w‖ := by
      simpa only [Complex.sub_im, hwreal, sub_zero] using Complex.abs_im_le_norm (z-w)
    have hgap := separated_conjugate_roots_have_imaginary_gap
      (P y) (hreal y) d (hsep y) z hz him
    exact (not_lt_of_ge hgap) (himnorm.trans_lt hnearGap)
  have hclosed : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    change ¬ (∀ z, (P x).eval z = 0 → z.im = 0) at hx
    push Not at hx
    obtain ⟨z, hz, him⟩ := hx
    obtain ⟨epsilon, hepsilon, hsmall⟩ := root_approximation_tolerance
      q hq |z.im| (max ‖z‖ 1) (abs_pos.mpr him) (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    filter_upwards [eventually_close_all_coefficients P q hdegree hc x epsilon hepsilon] with y hy
    have hycoeff : ∀ i, ‖(P y).coeff i - (P x).coeff i‖ < epsilon := by
      intro i
      simpa only [norm_sub_rev] using hy i
    obtain ⟨w, hw, hnear⟩ := Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt
      (f := P x) (g := P y) hepsilon hz (hmonic x) (hmonic y)
      (by rw [hdegree x, hdegree y]) hycoeff (IsAlgClosed.splits (P y))
    intro hyreal
    have hwzero : (P y).eval w = 0 := (Polynomial.mem_roots (hmonic y).ne_zero).mp hw
    have hwreal := hyreal w hwzero
    have himnorm : |z.im| ≤ ‖z - w‖ := by
      simpa only [Complex.sub_im, hwreal, sub_zero] using Complex.abs_im_le_norm (z-w)
    rw [hdegree x] at hnear
    exact (not_lt_of_ge himnorm) (hnear.trans hsmall)
  have hall : S = Set.univ := (show IsClopen S from ⟨hclosed, hopen⟩).eq_univ ⟨x0, hstart⟩
  intro x
  have hx : x ∈ S := by rw [hall]; trivial
  exact hx



/-- A monic polynomial root is bounded by the sum of the lower coefficient norms. -/
theorem monic_root_bound_by_coefficient_sum
    (P : Polynomial ℂ) (hp : P.Monic) (z : ℂ) (hz : P.eval z = 0) :
    ‖z‖ ≤ (∑ i ∈ Finset.range P.natDegree, ‖P.coeff i‖)+1 := by
  have hcb : P.cauchyBound ≤
      (∑ i ∈ Finset.range P.natDegree, ‖P.coeff i‖₊)+1 := by
    have hs : (Finset.range P.natDegree).sup (fun i => ‖P.coeff i‖₊) ≤
        ∑ i ∈ Finset.range P.natDegree, ‖P.coeff i‖₊ := by
      apply Finset.sup_le
      intro i hi
      exact Finset.single_le_sum (f := fun j => ‖P.coeff j‖₊)
        (fun j _ => (show (0 : NNReal) ≤ ‖P.coeff j‖₊ from bot_le)) hi
    simpa [Polynomial.cauchyBound, hp.leadingCoeff] using add_le_add_right hs 1
  have hroot := Polynomial.IsRoot.norm_lt_cauchyBound hp.ne_zero hz
  have hreal := NNReal.coe_le_coe.mpr (hroot.le.trans hcb)
  simpa only [NNReal.coe_add, NNReal.coe_sum, coe_nnnorm, NNReal.coe_one] using hreal

private theorem compact_fixed_degree_family_has_uniform_root_bound
    {A : Type*} [TopologicalSpace A] [CompactSpace A]
    (P : A → Polynomial ℂ) (q : ℕ)
    (hmonic : ∀ x, (P x).Monic) (hdegree : ∀ x, (P x).natDegree = q)
    (hc : ∀ i, Continuous (fun x => (P x).coeff i)) (x0 : A) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ x z, (P x).eval z = 0 → ‖z‖ ≤ R := by
  let S : A → ℝ := fun x => ∑ i ∈ Finset.range q, ‖(P x).coeff i‖
  have hS : Continuous S := by
    dsimp [S]
    exact continuous_finsetSum _ (fun i hi => (hc i).norm)
  obtain ⟨xmax, hxmax, hmax⟩ := isCompact_univ.exists_isMaxOn
    (show (Set.univ : Set A).Nonempty from ⟨x0, Set.mem_univ x0⟩) hS.continuousOn
  refine ⟨S xmax+1, ?_, ?_⟩
  · have hn : 0 ≤ S xmax := Finset.sum_nonneg (fun i hi => norm_nonneg _)
    linarith
  · intro x z hz
    have hroot := monic_root_bound_by_coefficient_sum (P x) (hmonic x) z hz
    rw [hdegree x] at hroot
    have hle : S x ≤ S xmax := hmax (Set.mem_univ x)
    change ‖z‖ ≤ S x+1 at hroot
    linarith

/-- A compact connected family of monic real polynomials with uniformly separated
distinct roots remains real-rooted when one member is real-rooted. Degree zero is included. -/
theorem compact_separated_real_family
    {A : Type*} [TopologicalSpace A] [PreconnectedSpace A] [CompactSpace A]
    (P : A → Polynomial ℂ) (q : ℕ)
    (hmonic : ∀ x, (P x).Monic) (hdegree : ∀ x, (P x).natDegree = q)
    (hc : ∀ i, Continuous (fun x => (P x).coeff i))
    (d : ℝ) (hd : 0 < d) (hreal : ∀ x i, ((P x).coeff i).im = 0)
    (hsep : ∀ x z w, (P x).eval z = 0 → (P x).eval w = 0 → z ≠ w → d ≤ ‖z - w‖)
    (x0 : A) (hstart : ∀ z, (P x0).eval z = 0 → z.im = 0) :
    ∀ x z, (P x).eval z = 0 → z.im = 0 := by
  by_cases hq : q = 0
  · intro x z hz
    have hone : P x = 1 := (hmonic x).natDegree_eq_zero.mp (by rw [hdegree x, hq])
    simp [hone] at hz
  obtain ⟨R,hR,hbound⟩ := compact_fixed_degree_family_has_uniform_root_bound
    P q hmonic hdegree hc x0
  exact separated_real_polynomial_family_preserves_root_reality
    P q (Nat.pos_of_ne_zero hq) hmonic hdegree hc R d hR hd hbound hreal hsep x0 hstart


#print axioms compact_separated_real_family

end D5.S3.Zeros.Jensen.CompactSeparatedRealContinuation
