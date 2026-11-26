/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteLocalRecovery
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteLocalRecovery
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff]
   utility: none
   digest: Local inversion of the normalized periodic two-site density on a fixed affine chart. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteDifferential
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FiniteDimensional
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Operator.Basic

/-! The radial column controls the derivative after trace normalization. -/

noncomputable section

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteLocalRecovery

open Matrix Set
open scoped Matrix.Norms.Elementwise Topology ComplexConjugate NNReal
open PeriodicMPSParentIntersection (Bond Word twoFlattening)
open PeriodicMPSTwoSiteAmbiguity (rawTwo)
open PeriodicMPSTwoSiteDifferential (chart augmented projective_rank_eight)
open UniformMPSExpectedDimensionRefutation (traceWord)

private abbrev Coord := Fin 4 → ℂ
private abbrev Bits := Fin 2 × Fin 2
private abbrev Density := Matrix Bits Bits ℂ
private abbrev Direction := Fin 4 × Fin 2

/-- The total squared mass of the periodic amplitude, read from its complete flattening. -/
def twoMass (A : Fin 2 → Bond) (r : ℕ) : ℝ :=
  (rawTwo A r).trace.re

/-- The trace-one two-site partial trace at positive mass. -/
def normalizedTwo (A : Fin 2 → Bond) (r : ℕ) : Density :=
  (twoMass A r)⁻¹ • rawTwo A r

private lemma trace_eq_sum (A : Fin 2 → Bond) (r : ℕ) :
    (rawTwo A r).trace =
      ((∑ p : Bits, ∑ b : Word (r + 2), Complex.normSq (twoFlattening A r p b)) : ℝ) := by
  simp only [rawTwo, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  push_cast
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun b _ => Complex.mul_conj _

private lemma mass_eq_sum (A : Fin 2 → Bond) (r : ℕ) :
    twoMass A r = ∑ p : Bits, ∑ b : Word (r + 2), Complex.normSq (twoFlattening A r p b) := by
  rw [twoMass, trace_eq_sum, Complex.ofReal_re]

private lemma mass_positive (A : Fin 2 → Bond) (r : ℕ) (h : rawTwo A r ≠ 0) :
    0 < twoMass A r := by
  rw [mass_eq_sum]
  apply lt_of_le_of_ne (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
  intro he
  apply h
  have he' (p : Bits) (b : Word (r + 2)) : twoFlattening A r p b = 0 := by
    have hp := (Finset.sum_eq_zero_iff_of_nonneg
      (fun (p : Bits) _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg
        (twoFlattening A r p _))).mp he.symm p (Finset.mem_univ p)
    exact Complex.normSq_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun (b : Word (r+2)) _ => Complex.normSq_nonneg (twoFlattening A r p b))).mp hp b
        (Finset.mem_univ b))
  simp [rawTwo, show twoFlattening A r = 0 from Matrix.ext fun p b => he' p b]

private lemma smooth_chart (a : ℂ) (i j k : Fin 2) :
    ContDiff ℝ 1 (fun x : Coord => chart a x i j k) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first | exact contDiff_const | exact contDiff_apply ℝ (fun _ : Fin 4 => ℂ) _

private lemma smooth_product (a : ℂ) (s : List (Fin 2)) (i j : Fin 2) :
    ContDiff ℝ 1 (fun x : Coord => (s.map (chart a x)).prod i j) := by
  induction s generalizing i j with
  | nil => exact contDiff_const
  | cons k s ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
    exact ContDiff.sum fun l _ => (smooth_chart a k i l).mul (ih l j)

private lemma smooth_flattening (r : ℕ) (a : ℂ) (p : Bits) (b : Word (r + 2)) :
    ContDiff ℝ 1 (fun x : Coord => twoFlattening (chart a x) r p b) := by
  simp only [twoFlattening, traceWord, Matrix.trace, Matrix.diag, List.ofFn_comp']
  exact ContDiff.sum fun i _ => smooth_product a _ i i

private lemma smooth_raw_entry (r : ℕ) (a : ℂ) (p q : Bits) :
    ContDiff ℝ 1 (fun x : Coord => rawTwo (chart a x) r p q) := by
  simp only [rawTwo, Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact ContDiff.sum fun b _ => (smooth_flattening r a p b).mul
    (Complex.conjCLE.contDiff.comp (smooth_flattening r a q b))

private lemma smooth_raw (r : ℕ) (a : ℂ) :
    ContDiff ℝ 1 (fun x : Coord => rawTwo (chart a x) r) := by
  exact contDiff_pi.mpr fun p => contDiff_pi.mpr fun q => smooth_raw_entry r a p q

private lemma smooth_mass (r : ℕ) (a : ℂ) :
    ContDiff ℝ 1 (fun x : Coord => twoMass (chart a x) r) := by
  exact Complex.reCLM.contDiff.comp
    (ContDiff.sum (s := Finset.univ) fun p _ => smooth_raw_entry r a p p)

private def axis (d : Direction) (j : Fin 4) : ℂ :=
  if j = d.1 then (if d.2 = 0 then 1 else Complex.I) else 0

private def axisCoeff (v : Coord) (d : Direction) : ℝ :=
  if d.2 = 0 then (v d.1).re else (v d.1).im

private lemma axis_expansion (v : Coord) :
    (∑ k : Fin 8, axisCoeff v (finProdFinEquiv.symm k) • axis (finProdFinEquiv.symm k)) = v := by
  calc
    _ = ∑ d : Direction, axisCoeff v d • axis d :=
      finProdFinEquiv.symm.sum_comp (fun d => axisCoeff v d • axis d)
    _ = v := ?_
  rw [Fintype.sum_prod_type]
  ext j
  simp only [Fin.sum_univ_two, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Complex.real_smul]
  rw [Finset.sum_eq_single j]
  · simp [axis, axisCoeff]
  · intro i _ hi
    simp [axis, Ne.symm hi]
  · simp

private lemma augmented_succ (r : ℕ) (a : ℂ) (x : Coord)
    (p q : Bits) (k : Fin 8) :
    augmented r a x (p, q) k.succ =
      fderiv ℝ (fun y : Coord => rawTwo (chart a y) r) x
        (axis (finProdFinEquiv.symm k)) p q := by
  let d : Direction := finProdFinEquiv.symm k
  let v := axis d
  let e := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Bits => ℂ) q).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Bits => Bits → ℂ) p)
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    have h := ((ContinuousLinearMap.id ℝ ℝ).smulRight v).hasFDerivAt (x := (0 : ℝ))
    simpa using (h.const_add x).hasDerivAt
  have hd := ((smooth_raw r a).differentiable (by norm_num) x).hasFDerivAt
  have hentry := e.hasFDerivAt.comp x hd
  have h := (hentry.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)).deriv
  have hfun : (e ∘ (fun y : Coord => rawTwo (chart a y) r)) ∘ (fun t : ℝ => x + t • v) =
      (fun t : ℝ => rawTwo (chart a (fun j => x j +
        if j = d.1 then
          (t : ℂ) * (if d.2 = 0 then 1 else Complex.I) else 0)) r p q) := by
    funext t
    change rawTwo (chart a (x + t • v)) r p q =
      rawTwo (chart a (fun j => x j + if j = d.1 then
        (t : ℂ) * (if d.2 = 0 then 1 else Complex.I) else 0)) r p q
    have heq : x + t • v = fun j => x j + if j = d.1 then
        (t : ℂ) * (if d.2 = 0 then 1 else Complex.I) else 0 := by
      funext j
      simp [v, axis, Pi.smul_apply, Complex.real_smul, mul_ite]
    rw [heq]
  rw [hfun] at h
  exact h

private lemma raw_ne_zero_of_minor (r : ℕ) (a : ℂ) (x : Coord)
    (rows : Fin 9 → Bits × Bits) (h : ((augmented r a x).submatrix rows id).det ≠ 0) :
    rawTwo (chart a x) r ≠ 0 := by
  intro hz
  apply h
  exact Matrix.det_eq_zero_of_column_eq_zero 0 fun i => by
    change rawTwo (chart a x) r (rows i).1 (rows i).2 = 0
    rw [hz, Matrix.zero_apply]

private lemma no_radial_tangent (r : ℕ) (a : ℂ) (x : Coord)
    (rows : Fin 9 → Bits × Bits) (h : ((augmented r a x).submatrix rows id).det ≠ 0)
    (v : Coord) (c : ℝ)
    (hv : fderiv ℝ (fun y : Coord => rawTwo (chart a y) r) x v =
      c • rawTwo (chart a x) r) : v = 0 := by
  let M := (augmented r a x).submatrix rows id
  let coeff : Fin 9 → ℂ := Fin.cons (-(c : ℂ))
    (fun k => (axisCoeff v (finProdFinEquiv.symm k) : ℂ))
  have hmul : M *ᵥ coeff = M *ᵥ 0 := by
    rw [Matrix.mulVec_zero]
    ext i
    have hv' := congrFun (congrFun hv (rows i).1) (rows i).2
    have hs := congrArg
      (fun w : Coord => fderiv ℝ (fun y : Coord => rawTwo (chart a y) r) x w
        (rows i).1 (rows i).2) (axis_expansion v)
    simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul] at hs hv'
    change (∑ k : Fin 9, augmented r a x (rows i) k * coeff k) = 0
    rw [Fin.sum_univ_succ]
    simp only [coeff, Fin.cons_zero, Fin.cons_succ]
    have hcol (k : Fin 8) := augmented_succ r a x (rows i).1 (rows i).2 k
    simp_rw [hcol]
    change rawTwo (chart a x) r (rows i).1 (rows i).2 * -(c : ℂ) + _ = 0
    simp_rw [mul_comm (_ : ℂ) (axisCoeff v _ : ℂ)]
    rw [hs, hv']
    ring
  have hc := Matrix.mulVec_injective_of_det_ne_zero h hmul
  rw [← axis_expansion v]
  apply Finset.sum_eq_zero
  intro k _
  have hk := congrFun hc k.succ
  have hreal : axisCoeff v (finProdFinEquiv.symm k) = 0 :=
    Complex.ofReal_injective (by simpa [coeff] using hk)
  rw [hreal, zero_smul]

private lemma normalized_derivative (r : ℕ) (a : ℂ) (x : Coord)
    (rows : Fin 9 → Bits × Bits) (h : ((augmented r a x).submatrix rows id).det ≠ 0) :
    let f := fun y : Coord => normalizedTwo (chart a y) r
    ContDiffAt ℝ 1 f x ∧ Function.Injective (fderiv ℝ f x) := by
  let m := fun y : Coord => twoMass (chart a y) r
  let g : Coord → Density := fun y => rawTwo (chart a y) r
  let f := fun y : Coord => normalizedTwo (chart a y) r
  have hm : ContDiff ℝ 1 m := smooth_mass r a
  have hpos : 0 < m x := mass_positive _ _ (raw_ne_zero_of_minor r a x rows h)
  have hcd : ContDiffAt ℝ 1 f x :=
    (hm.contDiffAt.inv hpos.ne').smul (smooth_raw r a).contDiffAt
  have hdf := (hcd.differentiableAt one_ne_zero).hasFDerivAt
  have hdm := ((hm.differentiable one_ne_zero) x).hasFDerivAt
  have hrescale : (fun y => m y • f y) =ᶠ[𝓝 x] g := by
    filter_upwards [hm.continuous.continuousAt.eventually_ne hpos.ne'] with y hy
    change m y • (m y)⁻¹ • g y = g y
    rw [smul_smul, mul_inv_cancel₀ hy, one_smul]
  have hder := ((hdm.smul hdf).congr_of_eventuallyEq hrescale.symm).fderiv
  refine ⟨hcd, (injective_iff_map_eq_zero (fderiv ℝ f x)).mpr fun v hv => ?_⟩
  apply no_radial_tangent r a x rows h v (fderiv ℝ m x v * (m x)⁻¹)
  calc
    fderiv ℝ g x v = (m x • fderiv ℝ f x + (fderiv ℝ m x).smulRight (f x)) v :=
      congrArg (fun D : Coord →L[ℝ] Density => D v) hder
    _ = _ := by
      simp only [_root_.add_apply, _root_.smul_apply, hv, smul_zero,
        zero_add, ContinuousLinearMap.smulRight_apply]
      exact smul_smul _ _ _

/-- At every ring length r + 4, a positive-mass open neighborhood on a fixed chart
admits a decoder of the actual normalized marginal through one real linear projection. -/
theorem normalized_local_recovery (r : ℕ) :
    ∃ (a : ℂ) (x : Coord) (U : Set Coord) (decode : Density → Coord) (L : ℝ),
      IsOpen U ∧ x ∈ U ∧
      (∀ y ∈ U, 0 < twoMass (chart a y) r) ∧
      InjOn (fun y => normalizedTwo (chart a y) r) U ∧
      (∀ y ∈ U, decode (normalizedTwo (chart a y) r) = y) ∧
      0 ≤ L ∧ ∀ y ∈ U, ∀ z ∈ U,
        ‖y - z‖ ≤ L * ‖normalizedTwo (chart a y) r - normalizedTwo (chart a z) r‖ := by
  obtain ⟨a, x, rows, h⟩ := projective_rank_eight r
  let f := fun y : Coord => normalizedTwo (chart a y) r
  obtain ⟨hf, hdf⟩ := normalized_derivative r a x rows h
  obtain ⟨P, hP⟩ := (fderiv ℝ f x).toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hdf)
  let p : Density →L[ℝ] Coord := P.toContinuousLinearMap
  have hp : p.comp (fderiv ℝ f x) = ContinuousLinearMap.id ℝ Coord := by
    apply ContinuousLinearMap.ext
    intro v
    exact LinearMap.congr_fun hP v
  let g := p ∘ f
  have hg : ContDiffAt ℝ 1 g x := p.contDiff.comp_contDiffAt x hf
  have hdg : HasFDerivAt g (ContinuousLinearEquiv.refl ℝ Coord : Coord →L[ℝ] Coord) x := by
    change HasFDerivAt g (ContinuousLinearMap.id ℝ Coord) x
    rw [← hp]
    exact p.hasFDerivAt.comp x (hf.differentiableAt one_ne_zero).hasFDerivAt
  have hstrict : HasStrictFDerivAt g (ContinuousLinearMap.id ℝ Coord) x :=
    hg.hasStrictFDerivAt' hdg one_ne_zero
  obtain ⟨s, hs, happrox⟩ := hstrict.approximates_deriv_on_nhds
    (Or.inr (by norm_num : (0 : ℝ≥0) < 1 / 2))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  let e := hg.toOpenPartialHomeomorph g hdg one_ne_zero
  have hx : x ∈ e.source := hg.mem_toOpenPartialHomeomorph_source hdg one_ne_zero
  let U := e.source ∩ {y | 0 < twoMass (chart a y) r} ∩ Metric.ball x ε
  have hU : IsOpen U := (e.open_source.inter (isOpen_lt continuous_const
    (smooth_mass r a).continuous)).inter Metric.isOpen_ball
  have hxU : x ∈ U :=
    ⟨⟨hx, mass_positive _ _ (raw_ne_zero_of_minor r a x rows h)⟩, Metric.mem_ball_self hε⟩
  have hinv : ∀ y ∈ U, (e.symm ∘ p) (f y) = y := fun y hy => e.left_inv hy.1.1
  obtain ⟨C, hC, hpbound⟩ := p.bound
  refine ⟨a, x, U, e.symm ∘ p, 2 * C, hU, hxU, fun _ hy => hy.1.2, ?_, hinv,
    mul_nonneg (by norm_num) hC.le, ?_⟩
  · intro y hy z hz hyz
    exact (hinv y hy).symm.trans ((congrArg (e.symm ∘ p) hyz).trans (hinv z hz))
  · intro y hy z hz
    have ha : ‖g y - g z - (y - z)‖ ≤ (1 / 2 : ℝ) * ‖y - z‖ := by
      simpa using happrox y (hball hy.2) z (hball hz.2)
    have ht : ‖y - z‖ ≤ ‖g y - g z‖ + ‖g y - g z - (y - z)‖ := by
      convert norm_sub_le (g y - g z) (g y - g z - (y - z)) using 2
      abel
    have hl : ‖g y - g z‖ ≤ C * ‖f y - f z‖ := by
      have hsub : p (f y - f z) = g y - g z := p.map_sub (f y) (f z)
      calc
        ‖g y - g z‖ = ‖p (f y - f z)‖ := congrArg norm hsub.symm
        _ ≤ _ := hpbound (f y - f z)
    change ‖y - z‖ ≤ 2 * C * ‖f y - f z‖
    rw [mul_assoc]
    linarith

#print axioms normalized_local_recovery

end D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteLocalRecovery
