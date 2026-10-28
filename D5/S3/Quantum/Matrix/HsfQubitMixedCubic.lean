/- GID: D5/S3/Quantum/Matrix/HsfQubitMixedCubic
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfQubitMixedCubic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.PosDef]
   utility: none
   digest: Six positive rank-one forms control the two-level mixed cubic trace coefficient. -/

/-
admission_basis: escape-witness
proof_shape: coefficient_compatibility: content
escape_witness: coordinate_mixed_cubic_bound; exact six-square trace certificate
The endpoint-to-scalar lifting is retained here only as consumed bind-only helpers;
it is not an independently frozen mathematical module.
The six-row mixed certificate is derived from the original ordered trace-word
coefficients. Its endpoint bound requires only the K constraints. Coordinate
and energy helpers are consumed by the final coefficient compatibility theorem.
The analytic derivative identification is a separate obligation; full HSF is open.
-/

module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic
public import D5.S3.Quantum.Matrix.HsfQubitCoupledScalar

/-! The original ordered trace-word coefficients are defined independently of
the six-square certificate. The identities below derive the certificate from
those coefficients. Identification with derivatives of the physical matrix
power function is a separate analytic obligation. Full HSF remains open.
Information-escape audits are unfinished: the eight attempted mixed registrations
report IE-C050, and the consumed endpoint-lifting helpers have no validated binding.
See https://github.com/the-omega-institute/trureturing/issues/23103. -/

@[expose] public section
noncomputable section
open Matrix
open scoped ComplexOrder

namespace D5.S3.Quantum.Matrix.HsfQubitCoupledCubic

abbrev Mat := _root_.Matrix (Fin 2) (Fin 2) ℂ

/-- The Hermitian matrix with prescribed real diagonal and complex upper entry. -/
def hermitian (a b : ℝ) (z : ℂ) : Mat := !![(a : ℂ), z; star z, (b : ℂ)]

/-- Real diagonal coordinates and conjugate off-diagonal entries give a Hermitian matrix. -/
theorem hermitian_isHermitian (a b : ℝ) (z : ℂ) :
    (hermitian a b z).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hermitian]

/-- Every complex Hermitian two by two matrix has these coordinates. -/
theorem hermitian_eq (H : Mat) (hH : H.IsHermitian) :
    H = hermitian (H 0 0).re (H 1 1).re (H 0 1) := by
  have hd (i : Fin 2) : (H i i).im = 0 := by
    have h := congrArg Complex.im (hH.apply i i)
    simp at h
    linarith
  have h10 : H 1 0 = star (H 0 1) := (hH.apply 1 0).symm
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermitian, h10, Complex.ext_iff, hd]

/-- PSD entry bounds require no invertibility, so they include singular endpoints. -/
private theorem psd_entries (a b : ℝ) (z : ℂ)
    (h : (hermitian a b z).PosSemidef) :
    0 ≤ a ∧ 0 ≤ b ∧ ‖z‖ ^ 2 ≤ a * b := by
  have ha := (Complex.nonneg_iff.mp (h.diag_nonneg (i := 0))).1
  have hb := (Complex.nonneg_iff.mp (h.diag_nonneg (i := 1))).1
  have hd := (Complex.nonneg_iff.mp h.det_nonneg).1
  simp [hermitian, Matrix.det_fin_two] at ha hb hd
  refine ⟨ha, hb, ?_⟩
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith [hd]

private theorem hermitian_sub (a b c d : ℝ) (z w : ℂ) :
    hermitian a b z - hermitian c d w = hermitian (a-c) (b-d) (z-w) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermitian]

private theorem hermitian_add (a b c d : ℝ) (z w : ℂ) :
    hermitian a b z + hermitian c d w = hermitian (a+c) (b+d) (z+w) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermitian]

private theorem hermitian_one : hermitian 1 1 0 = (1 : Mat) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermitian]

private theorem two_term_cauchy (p q r s : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    Real.sqrt (p*q) + Real.sqrt (r*s) ≤ Real.sqrt ((p+r)*(q+s)) := by
  have hf : ∀ i : Fin 2, 0 ≤ (![p,r] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i <;> simp [hp, hr]
  have hg : ∀ i : Fin 2, 0 ≤ (![q,s] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i <;> simp [hq, hs]
  have h := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (Fin 2)) hf hg
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    ← Real.sqrt_mul hp, ← Real.sqrt_mul hr, ← Real.sqrt_mul (add_nonneg hp hr)] using h

/-- Two original PSD endpoints constrain their sum of off-diagonal moduli jointly. -/
theorem endpoint_coupling (a b h k r s : ℝ) (z w : ℂ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hminus : (hermitian (a-h) (b-k) (-z)).PosSemidef)
    (kplus : (hermitian (1+r) (1+s) w).PosSemidef) :
    ‖z‖ + Real.sqrt (a*b) * ‖w‖ ≤
      Real.sqrt ((a-h+a*(1+r))*(b-k+b*(1+s))) := by
  obtain ⟨hp,hq,hz⟩ := psd_entries _ _ _ hminus
  obtain ⟨hr,hs,hw⟩ := psd_entries _ _ _ kplus
  simp only [norm_neg] at hz
  have hz' := Real.le_sqrt_of_sq_le hz
  have hw' := Real.le_sqrt_of_sq_le hw
  have hmul : Real.sqrt (a*b) * ‖w‖ ≤
      Real.sqrt ((a*(1+r))*(b*(1+s))) := by
    calc
      _ ≤ Real.sqrt (a*b) * Real.sqrt ((1+r)*(1+s)) :=
        mul_le_mul_of_nonneg_left hw' (Real.sqrt_nonneg _)
      _ = Real.sqrt ((a*(1+r))*(b*(1+s))) := by
        rw [← Real.sqrt_mul (mul_nonneg ha hb)]
        congr 1
        ring
  exact (add_le_add hz' hmul).trans
    (two_term_cauchy (a-h) (b-k) (a*(1+r)) (b*(1+s)) hp hq
      (mul_nonneg ha hr) (mul_nonneg hb hs))

/-- For a Hermitian two by two contraction, an entry row has squared mass at most one. -/
theorem contraction_row (r s : ℝ) (z : ℂ)
    (hp : (hermitian (1+r) (1+s) z).PosSemidef)
    (hm : (hermitian (1-r) (1-s) (-z)).PosSemidef) :
    ‖z‖ ^ 2 ≤ 1-r^2 := by
  obtain ⟨hrp,hsp,hzp⟩ := psd_entries _ _ _ hp
  obtain ⟨hrm,hsm,hzm⟩ := psd_entries _ _ _ hm
  simp only [norm_neg] at hzm
  by_cases h : -r ≤ s
  · have hb : (1-r)*(1-s) ≤ 1-r^2 := by nlinarith
    exact hzm.trans hb
  · have hb : (1+r)*(1+s) ≤ 1-r^2 := by nlinarith
    exact hzp.trans hb

/-- The displacement retains the coupled endpoint information instead of bounding its mean alone. -/
theorem displacement_coupling (a b m h k r s : ℝ) (z w : ℂ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hm : Real.sqrt (a*b) ≤ m)
    (hminus : (hermitian (a-h) (b-k) (-z)).PosSemidef)
    (kplus : (hermitian (1+r) (1+s) w).PosSemidef) :
    ‖z-(m : ℂ)*w‖ ≤ Real.sqrt ((2*a-(h-a*r))*(2*b-(k-b*s))) +
      (m-Real.sqrt (a*b))*‖w‖ := by
  have hm0 : 0 ≤ m := (Real.sqrt_nonneg _).trans hm
  have hcouple := endpoint_coupling a b h k r s z w ha hb hminus kplus
  have htriangle := norm_sub_le z ((m : ℂ)*w)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm0] at htriangle
  have heq : (a-h+a*(1+r))*(b-k+b*(1+s)) =
      (2*a-(h-a*r))*(2*b-(k-b*s)) := by ring
  rw [heq] at hcouple
  nlinarith

/-- A row bound in the diagonal weight, including all zero off-diagonal cases. -/
theorem displacement_row (a h r s : ℝ) (z : ℂ)
    (ha : 0 < a) (hh : h ≤ a)
    (hp : (hermitian (1+r) (1+s) z).PosSemidef)
    (hm : (hermitian (1-r) (1-s) (-z)).PosSemidef) :
    ‖z‖^2 ≤ 2*(2*a-(h-a*r))/a := by
  have hrow := contraction_row r s z hp hm
  have hsimple : ‖z‖^2 ≤ 2*(1+r) := by nlinarith [sq_nonneg (r+1)]
  apply (le_div_iff₀ ha).2
  nlinarith [mul_le_mul_of_nonneg_right hsimple ha.le]

private theorem trace_cube (u v : ℝ) (z : ℂ) :
    (Matrix.trace (hermitian u v z ^ 3)).re =
      (u+v)*(u^2-u*v+v^2+3*‖z‖^2) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [hermitian, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
    pow_succ] <;> ring_nf <;> simp

/-- The weighted quadratic trace in exact complex Hermitian coordinates. -/
theorem trace_weighted_square (a b u v : ℝ) (z : ℂ) :
    (Matrix.trace (hermitian a b 0 * hermitian u v z ^ 2)).re =
      a*(u^2+‖z‖^2)+b*(v^2+‖z‖^2) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [hermitian, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
    pow_succ] <;> ring_nf <;> simp

private def ScalarBound (a b m p : ℝ) : Prop :=
  ∀ (u v x w : ℝ), -2*a ≤ u → u ≤ 2*a → -2*b ≤ v → v ≤ 2*b →
    0 ≤ u+v → 0 ≤ x → 0 ≤ w →
    w ≤ Real.sqrt ((2*a-u)*(2*b-v)) + (m-Real.sqrt (a*b))*x →
    x^2 ≤ 2*(2*a-u)/a →
    (u+v)*(u^2-u*v+v^2+3*w^2) ≤
      2*(a*(u^2+w^2)+b*(v^2+w^2))+p*x^2

private theorem coordinate_displacement (a b m h k r s : ℝ) (z w : ℂ)
    (ha : 0 < a) (hb : 0 < b) (hm : Real.sqrt (a*b) ≤ m)
    (hp : (hermitian (a+h) (b+k) z).PosSemidef)
    (hn : (hermitian (a-h) (b-k) (-z)).PosSemidef)
    (kp : (hermitian (1+r) (1+s) w).PosSemidef)
    (kn : (hermitian (1-r) (1-s) (-w)).PosSemidef) :
    (-2*a ≤ h-a*r ∧ h-a*r ≤ 2*a ∧ -2*b ≤ k-b*s ∧ k-b*s ≤ 2*b) ∧
    ‖z-(m : ℂ)*w‖ ≤ Real.sqrt ((2*a-(h-a*r))*(2*b-(k-b*s))) +
      (m-Real.sqrt (a*b))*‖w‖ ∧
    ‖w‖^2 ≤ 2*(2*a-(h-a*r))/a := by
  obtain ⟨hpa,hpb,_⟩ := psd_entries _ _ _ hp
  obtain ⟨hna,hnb,_⟩ := psd_entries _ _ _ hn
  obtain ⟨kpa,kpb,_⟩ := psd_entries _ _ _ kp
  obtain ⟨kna,knb,_⟩ := psd_entries _ _ _ kn
  refine ⟨⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩,
    displacement_coupling a b m h k r s z w ha.le hb.le hm hn kp,
    displacement_row a h r s w ha (by linarith) kp kn⟩

private theorem scalar_positive_trace (a b m p h k r s : ℝ) (z w : ℂ)
    (ha : 0 < a) (hb : 0 < b) (hm : Real.sqrt (a*b) ≤ m)
    (hscalar : ScalarBound a b m p)
    (hp : (hermitian (a+h) (b+k) z).PosSemidef)
    (hn : (hermitian (a-h) (b-k) (-z)).PosSemidef)
    (kp : (hermitian (1+r) (1+s) w).PosSemidef)
    (kn : (hermitian (1-r) (1-s) (-w)).PosSemidef)
    (htrace : 0 ≤ (h-a*r)+(k-b*s)) :
    ((h-a*r)+(k-b*s))*((h-a*r)^2-(h-a*r)*(k-b*s)+(k-b*s)^2+
      3*‖z-(m : ℂ)*w‖^2) ≤
      2*(a*((h-a*r)^2+‖z-(m : ℂ)*w‖^2)+
        b*((k-b*s)^2+‖z-(m : ℂ)*w‖^2))+p*‖w‖^2 := by
  obtain ⟨⟨huL,huR,hvL,hvR⟩,hcouple,hrow⟩ :=
    coordinate_displacement a b m h k r s z w ha hb hm hp hn kp kn
  exact hscalar (h-a*r) (k-b*s) ‖w‖ ‖z-(m : ℂ)*w‖ huL huR hvL hvR
    htrace (norm_nonneg _) (norm_nonneg _) hcouple hrow

private theorem scalar_absolute_trace (a b m p h k r s : ℝ) (z w : ℂ)
    (ha : 0 < a) (hb : 0 < b) (hm : Real.sqrt (a*b) ≤ m)
    (hscalar : ScalarBound a b m p)
    (hp : (hermitian (a+h) (b+k) z).PosSemidef)
    (hn : (hermitian (a-h) (b-k) (-z)).PosSemidef)
    (kp : (hermitian (1+r) (1+s) w).PosSemidef)
    (kn : (hermitian (1-r) (1-s) (-w)).PosSemidef) :
    |((h-a*r)+(k-b*s))*((h-a*r)^2-(h-a*r)*(k-b*s)+(k-b*s)^2+
      3*‖z-(m : ℂ)*w‖^2)| ≤
      2*(a*((h-a*r)^2+‖z-(m : ℂ)*w‖^2)+
        b*((k-b*s)^2+‖z-(m : ℂ)*w‖^2))+p*‖w‖^2 := by
  have hfactor : 0 ≤ (h-a*r)^2-(h-a*r)*(k-b*s)+(k-b*s)^2+
      3*‖z-(m : ℂ)*w‖^2 := by
    nlinarith [sq_nonneg ((h-a*r)-(k-b*s)), sq_nonneg (h-a*r),
      sq_nonneg (k-b*s), sq_nonneg ‖z-(m : ℂ)*w‖]
  by_cases ht : 0 ≤ (h-a*r)+(k-b*s)
  · rw [abs_of_nonneg (mul_nonneg ht hfactor)]
    exact scalar_positive_trace a b m p h k r s z w ha hb hm hscalar hp hn kp kn ht
  · have hp' : (hermitian (a+(-h)) (b+(-k)) (-z)).PosSemidef := by
      simpa only [sub_eq_add_neg] using hn
    have hn' : (hermitian (a-(-h)) (b-(-k)) (-(-z))).PosSemidef := by
      simpa using hp
    have kp' : (hermitian (1+(-r)) (1+(-s)) (-w)).PosSemidef := by
      simpa only [sub_eq_add_neg] using kn
    have kn' : (hermitian (1-(-r)) (1-(-s)) (-(-w))).PosSemidef := by
      simpa using kp
    have ht' : 0 ≤ (-h-a*(-r))+(-k-b*(-s)) := by linarith
    have hbound := scalar_positive_trace a b m p (-h) (-k) (-r) (-s) (-z) (-w)
      ha hb hm hscalar hp' hn' kp' kn' ht'
    have hz : -z-(m : ℂ)*(-w) = -(z-(m : ℂ)*w) := by ring
    rw [hz, norm_neg, norm_neg] at hbound
    rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ht) hfactor)]
    convert hbound using 1 <;> ring

private theorem hermitian_swap_psd (a b : ℝ) (z : ℂ)
    (h : (hermitian a b z).PosSemidef) :
    (hermitian b a (star z)).PosSemidef := by
  convert h.submatrix (Equiv.swap (0 : Fin 2) 1) using 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermitian, Matrix.submatrix]

private theorem scalar_absolute_trace_swapped (a b m p h k r s : ℝ) (z w : ℂ)
    (ha : 0 < a) (hb : 0 < b) (hm : Real.sqrt (a*b) ≤ m)
    (hscalar : ScalarBound b a m p)
    (hp : (hermitian (a+h) (b+k) z).PosSemidef)
    (hn : (hermitian (a-h) (b-k) (-z)).PosSemidef)
    (kp : (hermitian (1+r) (1+s) w).PosSemidef)
    (kn : (hermitian (1-r) (1-s) (-w)).PosSemidef) :
    |((h-a*r)+(k-b*s))*((h-a*r)^2-(h-a*r)*(k-b*s)+(k-b*s)^2+
      3*‖z-(m : ℂ)*w‖^2)| ≤
      2*(a*((h-a*r)^2+‖z-(m : ℂ)*w‖^2)+
        b*((k-b*s)^2+‖z-(m : ℂ)*w‖^2))+p*‖w‖^2 := by
  have hp' := hermitian_swap_psd _ _ _ hp
  have hn' := hermitian_swap_psd _ _ _ hn
  have kp' := hermitian_swap_psd _ _ _ kp
  have kn' := hermitian_swap_psd _ _ _ kn
  simp only [star_neg] at hn' kn'
  have hbound := scalar_absolute_trace b a m p k h s r (star z) (star w)
    hb ha (by simpa only [mul_comm] using hm) hscalar hp' hn' kp' kn'
  have hz : star z-(m : ℂ)*star w = star (z-(m : ℂ)*w) := by
    simp [star_sub, star_mul, mul_comm]
  rw [hz, norm_star, norm_star] at hbound
  convert hbound using 1 <;> ring

/-- Multiplication by a real symmetric two point kernel, with its diagonal weights explicit. -/
def weightedImage (a b m : ℝ) (K : Mat) : Mat :=
  !![(a : ℂ)*K 0 0, (m : ℂ)*K 0 1; (m : ℂ)*K 1 0, (b : ℂ)*K 1 1]

/-- The kernel action preserves the exact Hermitian coordinates. -/
theorem weightedImage_hermitian (a b m r s : ℝ) (z : ℂ) :
    weightedImage a b m (hermitian r s z) =
      hermitian (a*r) (b*s) ((m : ℂ)*z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weightedImage, hermitian, mul_comm]

private theorem matrix_bound_of_scalar (a b m p : ℝ) (H K : Mat)
    (ha : 0 < a) (hb : 0 < b) (hm : Real.sqrt (a*b) ≤ m)
    (hscalar : ScalarBound a b m p ∨ ScalarBound b a m p)
    (hH : H.IsHermitian) (hK : K.IsHermitian)
    (hp : (hermitian a b 0 + H).PosSemidef)
    (hn : (hermitian a b 0 - H).PosSemidef)
    (kp : (1+K).PosSemidef) (kn : (1-K).PosSemidef) :
    |(Matrix.trace ((H-weightedImage a b m K)^3)).re| ≤
      2*(Matrix.trace (hermitian a b 0*(H-weightedImage a b m K)^2)).re+
        p*‖K 0 1‖^2 := by
  have hHrep := hermitian_eq H hH
  have hKrep := hermitian_eq K hK
  rw [hHrep, hermitian_add] at hp
  simp only [zero_add] at hp
  rw [hHrep, hermitian_sub] at hn
  simp only [zero_sub] at hn
  rw [← hermitian_one, hKrep, hermitian_add] at kp
  simp only [zero_add] at kp
  rw [← hermitian_one, hKrep, hermitian_sub] at kn
  simp only [zero_sub] at kn
  rw [hHrep, hKrep, weightedImage_hermitian, hermitian_sub, trace_cube,
    trace_weighted_square]
  simp only [hermitian, Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases hscalar with hscalar | hscalar
  · exact scalar_absolute_trace a b m p (H 0 0).re (H 1 1).re
      (K 0 0).re (K 1 1).re (H 0 1) (K 0 1) ha hb hm hscalar hp hn kp kn
  · exact scalar_absolute_trace_swapped a b m p (H 0 0).re (H 1 1).re
      (K 0 0).re (K 1 1).re (H 0 1) (K 0 1) ha hb hm hscalar hp hn kp kn

/-- The full coupled pure cubic inequality for complex Hermitian qubit matrices.
All four PSD endpoints may be singular. This is a supplier for the HSF problem,
not a resolution in arbitrary dimension or at a general second-variable base. -/
theorem coupled_cubic_compatibility (a b : ℝ) (H K : Mat)
    (ha : 0 < a) (hb : 0 < b) (hH : H.IsHermitian) (hK : K.IsHermitian)
    (hp : (hermitian a b 0 + H).PosSemidef)
    (hn : (hermitian a b 0 - H).PosSemidef)
    (kp : (1+K).PosSemidef) (kn : (1-K).PosSemidef) :
    |(Matrix.trace ((H-weightedImage a b (HsfQubitCoupledScalar.mean a b) K)^3)).re| ≤
      2*(Matrix.trace (hermitian a b 0*
        (H-weightedImage a b (HsfQubitCoupledScalar.mean a b) K)^2)).re+
        HsfQubitCoupledScalar.penalty a b*‖K 0 1‖^2 := by
  have hsupplier (c d : ℝ) (hd : 0 < d) (hcd : d ≤ c) :
      ScalarBound c d (HsfQubitCoupledScalar.mean c d) (HsfQubitCoupledScalar.penalty c d) := by
    intro u v x w huL huR hvL hvR htrace hx hw hcouple hrow
    exact HsfQubitCoupledScalar.coupled_cubic_le c d u v x w hd hcd huL huR hvL hvR
      htrace hx hw hcouple hrow
  apply matrix_bound_of_scalar a b (HsfQubitCoupledScalar.mean a b)
    (HsfQubitCoupledScalar.penalty a b) H K ha hb
    (sub_nonneg.mp (HsfQubitCoupledScalar.excess_nonneg a b ha hb)) ?_ hH hK hp hn kp kn
  rcases le_total b a with hab | hab
  · exact Or.inl (hsupplier a b hb hab)
  · apply Or.inr
    have hm : HsfQubitCoupledScalar.mean b a = HsfQubitCoupledScalar.mean a b := by
      unfold HsfQubitCoupledScalar.mean
      congr 1 <;> ring
    have hp' : HsfQubitCoupledScalar.penalty b a = HsfQubitCoupledScalar.penalty a b := by
      unfold HsfQubitCoupledScalar.penalty
      congr 1 <;> ring
    simpa only [hm, hp'] using hsupplier b a ha hab

#print axioms endpoint_coupling
#print axioms contraction_row
#print axioms coupled_cubic_compatibility

end D5.S3.Quantum.Matrix.HsfQubitCoupledCubic


namespace D5.S3.Quantum.Matrix.HsfQubitMixedCubic
open HsfQubitCoupledCubic

section Coefficients
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual second-order ordered trace-word coefficient for alpha=3 at Y=I. -/
def traceCoefficient2 (X H K : Matrix n n ℂ) : ℂ :=
  3*Matrix.trace (H*H*X) - 2*Matrix.trace (H*K*X*X) -
  2*Matrix.trace (H*X*K*X) - 2*Matrix.trace (H*X*X*K) +
  (5/3)*Matrix.trace (K*K*X*X*X) + (4/3)*Matrix.trace (K*X*K*X*X)

/-- The actual third-order ordered trace-word coefficient, with no commuting of factors. -/
def traceCoefficient3 (X H K : Matrix n n ℂ) : ℂ :=
  Matrix.trace (H*H*H) - 2*Matrix.trace (H*H*K*X) -
  2*Matrix.trace (H*H*X*K) - 2*Matrix.trace (H*K*H*X) +
  (5/3)*Matrix.trace (H*K*K*X*X) + (4/3)*Matrix.trace (H*K*X*K*X) +
  (4/3)*Matrix.trace (H*K*X*X*K) + (5/3)*Matrix.trace (H*X*K*K*X) +
  (4/3)*Matrix.trace (H*X*K*X*K) + (5/3)*Matrix.trace (H*X*X*K*K) -
  (40/27)*Matrix.trace (K*K*K*X*X*X) - (10/9)*Matrix.trace (K*K*X*K*X*X) -
  (10/9)*Matrix.trace (K*K*X*X*K*X) - (8/27)*Matrix.trace (K*X*K*X*K*X)

/-- The real second coefficient, to be matched with one half of the Hessian. -/
def coefficient2 (X H K : Matrix n n ℂ) : ℝ := (traceCoefficient2 X H K).re

/-- The real third coefficient, to be matched with one sixth of the third derivative. -/
def coefficient3 (X H K : Matrix n n ℂ) : ℝ := (traceCoefficient3 X H K).re


/-- The exact second trace jet is twice the original ordered coefficient.
This is a cyclic trace identity in arbitrary finite dimension. -/
theorem trace_jet_coefficient2 (X H K : Matrix n n ℂ) :
    let L := H-(2/3 : ℝ) • (X*K)
    let M := -(4/3 : ℝ) • (H*K)+(10/9 : ℝ) • (X*K^2)
    Matrix.trace ((3 : ℝ) • (M*X*X)+(6 : ℝ) • (L*L*X)) =
      2*traceCoefficient2 X H K := by
  dsimp only
  have h_hxh : Matrix.trace (H*(X*(H))) = Matrix.trace (H*(H*(X))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (H*X) (H))
  have h_xhh : Matrix.trace (X*(H*(H))) = Matrix.trace (H*(H*(X))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X) (H*H))
  have h_kxxh : Matrix.trace (K*(X*(X*(H)))) = Matrix.trace (H*(K*(X*(X)))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (K*X*X) (H))
  have h_xxhk : Matrix.trace (X*(X*(H*(K)))) = Matrix.trace (H*(K*(X*(X)))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X*X) (H*K))
  have h_xhkx : Matrix.trace (X*(H*(K*(X)))) = Matrix.trace (H*(K*(X*(X)))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X) (H*K*X))
  have h_xkxh : Matrix.trace (X*(K*(X*(H)))) = Matrix.trace (H*(X*(K*(X)))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X*K*X) (H))
  have h_kxhx : Matrix.trace (K*(X*(H*(X)))) = Matrix.trace (H*(X*(K*(X)))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (K*X) (H*X))
  have h_xhxk : Matrix.trace (X*(H*(X*(K)))) = Matrix.trace (H*(X*(K*(X)))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X) (H*X*K))
  have h_xxkh : Matrix.trace (X*(X*(K*(H)))) = Matrix.trace (H*(X*(X*(K)))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X*X*K) (H))
  have h_xkhx : Matrix.trace (X*(K*(H*(X)))) = Matrix.trace (H*(X*(X*(K)))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X*K) (H*X))
  have h_khxx : Matrix.trace (K*(H*(X*(X)))) = Matrix.trace (H*(X*(X*(K)))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (K) (H*X*X))
  have h_kxxxk : Matrix.trace (K*(X*(X*(X*(K))))) = Matrix.trace (K*(K*(X*(X*(X))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (K*X*X*X) (K))
  have h_xxxkk : Matrix.trace (X*(X*(X*(K*(K))))) = Matrix.trace (K*(K*(X*(X*(X))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X*X*X) (K*K))
  have h_xxkkx : Matrix.trace (X*(X*(K*(K*(X))))) = Matrix.trace (K*(K*(X*(X*(X))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X*X) (K*K*X))
  have h_xkkxx : Matrix.trace (X*(K*(K*(X*(X))))) = Matrix.trace (K*(K*(X*(X*(X))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X) (K*K*X*X))
  have h_xkxxk : Matrix.trace (X*(K*(X*(X*(K))))) = Matrix.trace (K*(X*(K*(X*(X))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X*K*X*X) (K))
  have h_kxxkx : Matrix.trace (K*(X*(X*(K*(X))))) = Matrix.trace (K*(X*(K*(X*(X))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (K*X*X) (K*X))
  have h_xxkxk : Matrix.trace (X*(X*(K*(X*(K))))) = Matrix.trace (K*(X*(K*(X*(X))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X*X) (K*X*K))
  have h_xkxkx : Matrix.trace (X*(K*(X*(K*(X))))) = Matrix.trace (K*(X*(K*(X*(X))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X) (K*X*K*X))
  simp only [traceCoefficient2, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add,
    Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_sub, Matrix.trace_smul, Complex.real_smul, pow_succ, pow_zero,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  simp only [h_hxh, h_xhh, h_kxxh, h_xxhk, h_xhkx, h_xkxh, h_kxhx, h_xhxk, h_xxkh, h_xkhx, h_khxx, h_kxxxk, h_xxxkk, h_xxkkx, h_xkkxx, h_xkxxk, h_kxxkx, h_xxkxk, h_xkxkx]
  push_cast
  ring

/-- The exact third trace jet is six times the original ordered coefficient.
The proof keeps every noncommuting word until applying trace cyclicity. -/
theorem trace_jet_coefficient3 (X H K : Matrix n n ℂ) :
    let L := H-(2/3 : ℝ) • (X*K)
    let M := -(4/3 : ℝ) • (H*K)+(10/9 : ℝ) • (X*K^2)
    let N := (10/3 : ℝ) • (H*K^2)-(80/27 : ℝ) • (X*K^3)
    Matrix.trace ((3 : ℝ) • (N*X*X)+(9 : ℝ) • (M*L*X)+
      (9 : ℝ) • (M*X*L)+(6 : ℝ) • (L*L*L)) =
      6*traceCoefficient3 X H K := by
  dsimp only
  have h_hkxh : Matrix.trace (H*(K*(X*(H)))) = Matrix.trace (H*(H*(K*(X)))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (H*K*X) (H))
  have h_kxhh : Matrix.trace (K*(X*(H*(H)))) = Matrix.trace (H*(H*(K*(X)))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (K*X) (H*H))
  have h_xhhk : Matrix.trace (X*(H*(H*(K)))) = Matrix.trace (H*(H*(K*(X)))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X) (H*H*K))
  have h_hxkh : Matrix.trace (H*(X*(K*(H)))) = Matrix.trace (H*(H*(X*(K)))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (H*X*K) (H))
  have h_xkhh : Matrix.trace (X*(K*(H*(H)))) = Matrix.trace (H*(H*(X*(K)))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X*K) (H*H))
  have h_khhx : Matrix.trace (K*(H*(H*(X)))) = Matrix.trace (H*(H*(X*(K)))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (K) (H*H*X))
  have h_khxh : Matrix.trace (K*(H*(X*(H)))) = Matrix.trace (H*(K*(H*(X)))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (K*H*X) (H))
  have h_hxhk : Matrix.trace (H*(X*(H*(K)))) = Matrix.trace (H*(K*(H*(X)))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (H*X) (H*K))
  have h_xhkh : Matrix.trace (X*(H*(K*(H)))) = Matrix.trace (H*(K*(H*(X)))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X) (H*K*H))
  have h_kkxxh : Matrix.trace (K*(K*(X*(X*(H))))) = Matrix.trace (H*(K*(K*(X*(X))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (K*K*X*X) (H))
  have h_kxxhk : Matrix.trace (K*(X*(X*(H*(K))))) = Matrix.trace (H*(K*(K*(X*(X))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (K*X*X) (H*K))
  have h_xxhkk : Matrix.trace (X*(X*(H*(K*(K))))) = Matrix.trace (H*(K*(K*(X*(X))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X*X) (H*K*K))
  have h_xhkkx : Matrix.trace (X*(H*(K*(K*(X))))) = Matrix.trace (H*(K*(K*(X*(X))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X) (H*K*K*X))
  have h_kxkxh : Matrix.trace (K*(X*(K*(X*(H))))) = Matrix.trace (H*(K*(X*(K*(X))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (K*X*K*X) (H))
  have h_xkxhk : Matrix.trace (X*(K*(X*(H*(K))))) = Matrix.trace (H*(K*(X*(K*(X))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X*K*X) (H*K))
  have h_kxhkx : Matrix.trace (K*(X*(H*(K*(X))))) = Matrix.trace (H*(K*(X*(K*(X))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (K*X) (H*K*X))
  have h_xhkxk : Matrix.trace (X*(H*(K*(X*(K))))) = Matrix.trace (H*(K*(X*(K*(X))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X) (H*K*X*K))
  have h_kxxkh : Matrix.trace (K*(X*(X*(K*(H))))) = Matrix.trace (H*(K*(X*(X*(K))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (K*X*X*K) (H))
  have h_xxkhk : Matrix.trace (X*(X*(K*(H*(K))))) = Matrix.trace (H*(K*(X*(X*(K))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X*X*K) (H*K))
  have h_xkhkx : Matrix.trace (X*(K*(H*(K*(X))))) = Matrix.trace (H*(K*(X*(X*(K))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X*K) (H*K*X))
  have h_khkxx : Matrix.trace (K*(H*(K*(X*(X))))) = Matrix.trace (H*(K*(X*(X*(K))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (K) (H*K*X*X))
  have h_xkkxh : Matrix.trace (X*(K*(K*(X*(H))))) = Matrix.trace (H*(X*(K*(K*(X))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X*K*K*X) (H))
  have h_kkxhx : Matrix.trace (K*(K*(X*(H*(X))))) = Matrix.trace (H*(X*(K*(K*(X))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (K*K*X) (H*X))
  have h_kxhxk : Matrix.trace (K*(X*(H*(X*(K))))) = Matrix.trace (H*(X*(K*(K*(X))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (K*X) (H*X*K))
  have h_xhxkk : Matrix.trace (X*(H*(X*(K*(K))))) = Matrix.trace (H*(X*(K*(K*(X))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X) (H*X*K*K))
  have h_xkxkh : Matrix.trace (X*(K*(X*(K*(H))))) = Matrix.trace (H*(X*(K*(X*(K))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X*K*X*K) (H))
  have h_kxkhx : Matrix.trace (K*(X*(K*(H*(X))))) = Matrix.trace (H*(X*(K*(X*(K))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (K*X*K) (H*X))
  have h_xkhxk : Matrix.trace (X*(K*(H*(X*(K))))) = Matrix.trace (H*(X*(K*(X*(K))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X*K) (H*X*K))
  have h_khxkx : Matrix.trace (K*(H*(X*(K*(X))))) = Matrix.trace (H*(X*(K*(X*(K))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (K) (H*X*K*X))
  have h_xxkkh : Matrix.trace (X*(X*(K*(K*(H))))) = Matrix.trace (H*(X*(X*(K*(K))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X*X*K*K) (H))
  have h_xkkhx : Matrix.trace (X*(K*(K*(H*(X))))) = Matrix.trace (H*(X*(X*(K*(K))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X*K*K) (H*X))
  have h_kkhxx : Matrix.trace (K*(K*(H*(X*(X))))) = Matrix.trace (H*(X*(X*(K*(K))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (K*K) (H*X*X))
  have h_khxxk : Matrix.trace (K*(H*(X*(X*(K))))) = Matrix.trace (H*(X*(X*(K*(K))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (K) (H*X*X*K))
  have h_kkxxxk : Matrix.trace (K*(K*(X*(X*(X*(K)))))) = Matrix.trace (K*(K*(K*(X*(X*(X)))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (K*K*X*X*X) (K))
  have h_kxxxkk : Matrix.trace (K*(X*(X*(X*(K*(K)))))) = Matrix.trace (K*(K*(K*(X*(X*(X)))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (K*X*X*X) (K*K))
  have h_xxxkkk : Matrix.trace (X*(X*(X*(K*(K*(K)))))) = Matrix.trace (K*(K*(K*(X*(X*(X)))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X*X*X) (K*K*K))
  have h_xxkkkx : Matrix.trace (X*(X*(K*(K*(K*(X)))))) = Matrix.trace (K*(K*(K*(X*(X*(X)))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X*X) (K*K*K*X))
  have h_xkkkxx : Matrix.trace (X*(K*(K*(K*(X*(X)))))) = Matrix.trace (K*(K*(K*(X*(X*(X)))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X) (K*K*K*X*X))
  have h_kxkxxk : Matrix.trace (K*(X*(K*(X*(X*(K)))))) = Matrix.trace (K*(K*(X*(K*(X*(X)))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (K*X*K*X*X) (K))
  have h_xkxxkk : Matrix.trace (X*(K*(X*(X*(K*(K)))))) = Matrix.trace (K*(K*(X*(K*(X*(X)))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X*K*X*X) (K*K))
  have h_kxxkkx : Matrix.trace (K*(X*(X*(K*(K*(X)))))) = Matrix.trace (K*(K*(X*(K*(X*(X)))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (K*X*X) (K*K*X))
  have h_xxkkxk : Matrix.trace (X*(X*(K*(K*(X*(K)))))) = Matrix.trace (K*(K*(X*(K*(X*(X)))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X*X) (K*K*X*K))
  have h_xkkxkx : Matrix.trace (X*(K*(K*(X*(K*(X)))))) = Matrix.trace (K*(K*(X*(K*(X*(X)))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X) (K*K*X*K*X))
  have h_kxxkxk : Matrix.trace (K*(X*(X*(K*(X*(K)))))) = Matrix.trace (K*(K*(X*(X*(K*(X)))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (K*X*X*K*X) (K))
  have h_xxkxkk : Matrix.trace (X*(X*(K*(X*(K*(K)))))) = Matrix.trace (K*(K*(X*(X*(K*(X)))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X*X*K*X) (K*K))
  have h_xkxkkx : Matrix.trace (X*(K*(X*(K*(K*(X)))))) = Matrix.trace (K*(K*(X*(X*(K*(X)))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X*K*X) (K*K*X))
  have h_kxkkxx : Matrix.trace (K*(X*(K*(K*(X*(X)))))) = Matrix.trace (K*(K*(X*(X*(K*(X)))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (K*X) (K*K*X*X))
  have h_xkkxxk : Matrix.trace (X*(K*(K*(X*(X*(K)))))) = Matrix.trace (K*(K*(X*(X*(K*(X)))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X) (K*K*X*X*K))
  have h_xkxkxk : Matrix.trace (X*(K*(X*(K*(X*(K)))))) = Matrix.trace (K*(X*(K*(X*(K*(X)))))) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (X) (K*X*K*X*K))
  simp only [traceCoefficient3, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add,
    Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_sub, Matrix.trace_smul, Complex.real_smul, pow_succ, pow_zero,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  simp only [h_hkxh, h_kxhh, h_xhhk, h_hxkh, h_xkhh, h_khhx, h_khxh, h_hxhk, h_xhkh, h_kkxxh, h_kxxhk, h_xxhkk, h_xhkkx, h_kxkxh, h_xkxhk, h_kxhkx, h_xhkxk, h_kxxkh, h_xxkhk, h_xkhkx, h_khkxx, h_xkkxh, h_kkxhx, h_kxhxk, h_xhxkk, h_xkxkh, h_kxkhx, h_xkhxk, h_khxkx, h_xxkkh, h_xkkhx, h_kkhxx, h_khxxk, h_kkxxxk, h_kxxxkk, h_xxxkkk, h_xxkkkx, h_xkkkxx, h_kxkxxk, h_xkxxkk, h_kxxkkx, h_xxkkxk, h_xkkxkx, h_kxxkxk, h_xxkxkk, h_xkxkkx, h_kxkkxx, h_xkkxxk, h_xkxkxk]
  push_cast
  ring


end Coefficients

/- The spectral argument is copied from
`D5/S3/Weil/ZetaLinear/RankTrace.lean`,
`RHLinalg.trace_mul_nonneg_of_posSemidef` (lines 123--138 at dev 25679597af3),
ported there from anthropics/zeta-23-lean
3635e74826a4c1fcece7d1cd2b6fa75e43a00510.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the repository LICENSE.
SPDX-License-Identifier: Apache-2.0
That source is a legacy non-module, so this consumed local bridge keeps the
present public module importable by the analytic derivative supplier. -/
private theorem trace_mul_nonneg_of_posSemidef
    {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [RCLike 𝕜]
    {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ RCLike.re (A * B).trace := by
  rw [hA.isHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply, mul_assoc,
    trace_mul_comm, ← mul_assoc]
  set M := star (hA.isHermitian.eigenvectorUnitary : Matrix n n 𝕜) * B *
    (hA.isHermitian.eigenvectorUnitary : Matrix n n 𝕜) with hM_def
  have hM : M.PosSemidef := hB.conjTranspose_mul_mul_same _
  simp only [trace, diag_apply, mul_diagonal, Function.comp_apply, map_sum,
    RCLike.mul_re, RCLike.ofReal_re, RCLike.ofReal_im, mul_zero, sub_zero]
  refine Finset.sum_nonneg fun i _ => ?_
  exact mul_nonneg (RCLike.nonneg_iff.mp hM.diag_nonneg).1 (hA.eigenvalues_nonneg i)

def f (a b : ℝ) : ℝ := 2*(a+2*b)/(3*(a+b))
def q (a b : ℝ) : ℝ := -(a-b)*(3*a^2+9*a*b+8*b^2)/(18*(a+b)^2)
def c (a b : ℝ) : ℝ := (a-b)^2*(2*a+3*b)/(a+b)^2
def j (a b : ℝ) : ℝ := b^2/(3*(a+b))
def d (a b : ℝ) : ℝ :=
  (a-b)^2*(a+2*b)*(7*a^2+14*a*b+4*b^2)/(36*(a+b)^2)

def rowGram (x y : ℂ) : Mat :=
  Matrix.vecMulVec (star (![x,y] : Fin 2 → ℂ)) (![x,y] : Fin 2 → ℂ)

private theorem rowGram_psd (x y : ℂ) : (rowGram x y).PosSemidef :=
  Matrix.posSemidef_vecMulVec_star_self _

/-- The six weighted row-Gram squares, valid also when the two spectral levels coincide. -/
def mixedMatrix (a b u v : ℝ) (w z : ℂ) : Mat :=
  (9*a) • rowGram (u : ℂ) ((f a b : ℂ)*w+(q a b : ℂ)*z) +
  c a b • rowGram 0 (w+(j a b : ℂ)*z) + d a b • rowGram 0 z +
  (9*b) • rowGram ((f b a : ℂ)*star w+(q b a : ℂ)*star z) (v : ℂ) +
  c b a • rowGram (star w+(j b a : ℂ)*star z) 0 + d b a • rowGram (star z) 0

/-- The certificate is positive for arbitrary displacement entries, without any H endpoint premise. -/
theorem mixedMatrix_posSemidef (a b u v : ℝ) (w z : ℂ)
    (ha : 0 < a) (hb : 0 < b) : (mixedMatrix a b u v w z).PosSemidef := by
  have hc (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 ≤ c a b := by
    unfold c
    positivity
  have hd (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 ≤ d a b := by
    unfold d
    positivity
  have h1 := (rowGram_psd (u : ℂ) ((f a b : ℂ)*w+(q a b : ℂ)*z)).smul
    (show 0 ≤ 9*a by positivity)
  have h2 := (rowGram_psd 0 (w+(j a b : ℂ)*z)).smul (hc a b ha hb)
  have h3 := (rowGram_psd 0 z).smul (hd a b ha hb)
  have h4 := (rowGram_psd ((f b a : ℂ)*star w+(q b a : ℂ)*star z) (v : ℂ)).smul
    (show 0 ≤ 9*b by positivity)
  have h5 := (rowGram_psd (star w+(j b a : ℂ)*star z) 0).smul (hc b a hb ha)
  have h6 := (rowGram_psd (star z) 0).smul (hd b a hb ha)
  exact ((((h1.add h2).add h3).add h4).add h5).add h6

private theorem energy_identity_complex (a b u v r s : ℝ) (w z : ℂ)
    (hab : a+b ≠ 0) :
    traceCoefficient2 (hermitian a b 0)
      (hermitian u v w + weightedImage a b
        (2*(a^2+a*b+b^2)/(3*(a+b))) (hermitian r s z)) (hermitian r s z) =
    3*Matrix.trace (hermitian a b 0*(hermitian u v w)^2) +
      (((a-b)^2*(a^2+3*a*b+b^2)/(3*(a+b)) : ℝ) : ℂ)*(star z*z) := by
  have habC : (a : ℂ)+(b : ℂ) ≠ 0 := by exact_mod_cast hab
  simp [traceCoefficient2, hermitian, weightedImage, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_two, pow_succ]
  push_cast
  field_simp [habC]
  ring

set_option maxRecDepth 8192 in
private theorem mixed_identity_complex (a b u v r s : ℝ) (w z : ℂ)
    (hab : a+b ≠ 0) :
    3*Matrix.trace ((hermitian u v w)^3) -
      3*traceCoefficient3 (hermitian a b 0)
      (hermitian u v w + weightedImage a b
        (2*(a^2+a*b+b^2)/(3*(a+b))) (hermitian r s z)) (hermitian r s z) =
      Matrix.trace (hermitian r s z*mixedMatrix a b u v w z) := by
  have habC : (a : ℂ)+(b : ℂ) ≠ 0 := by exact_mod_cast hab
  have hbaC : (b : ℂ)+(a : ℂ) ≠ 0 := by simpa only [add_comm] using habC
  simp [traceCoefficient3, hermitian, weightedImage, mixedMatrix, rowGram,
    Matrix.trace, Matrix.mul_apply, Matrix.vecMulVec, Fin.sum_univ_two,
    Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail, Pi.smul_apply,
    Complex.real_smul, f, q, c, j, d, pow_succ]
  push_cast
  simp only [map_ofNat, map_add, map_sub, map_mul, map_div₀, map_pow, map_neg,
    RCLike.conj_ofReal, starRingEnd_self_apply]
  field_simp [habC, hbaC]
  ring

set_option maxRecDepth 8192 in
private theorem mass_identity_complex (a b u v : ℝ) (w z : ℂ)
    (hab : a+b ≠ 0) :
    Matrix.trace (mixedMatrix a b u v w z) =
      9*Matrix.trace (hermitian a b 0*(hermitian u v w)^2) +
      (((a-b)^2*(a^2+3*a*b+b^2)/(a+b) : ℝ) : ℂ)*(star z*z) := by
  have habC : (a : ℂ)+(b : ℂ) ≠ 0 := by exact_mod_cast hab
  have hbaC : (b : ℂ)+(a : ℂ) ≠ 0 := by simpa only [add_comm] using habC
  simp [hermitian, mixedMatrix, rowGram, Matrix.trace, Matrix.mul_apply,
    Matrix.vecMulVec, Fin.sum_univ_two, Matrix.smul_apply, Matrix.vecHead,
    Matrix.vecTail, Pi.smul_apply, Complex.real_smul,
    f, q, c, j, d, pow_succ]
  push_cast
  simp only [map_ofNat, map_add, map_sub, map_mul, map_div₀, map_pow, map_neg,
    RCLike.conj_ofReal, starRingEnd_self_apply]
  field_simp [habC, hbaC]
  ring

/-- The Hessian energy is obtained from the original coefficient, not assumed. -/
theorem coordinate_energy_identity (a b u v r s : ℝ) (w z : ℂ)
    (hab : a+b ≠ 0) :
    coefficient2 (hermitian a b 0)
      (hermitian u v w + weightedImage a b
        (2*(a^2+a*b+b^2)/(3*(a+b))) (hermitian r s z)) (hermitian r s z) =
    3*(Matrix.trace (hermitian a b 0*(hermitian u v w)^2)).re +
      ((a-b)^2*(a^2+3*a*b+b^2)/(3*(a+b)))*‖z‖^2 := by
  have h := congrArg Complex.re (energy_identity_complex a b u v r s w z hab)
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] at h
  simpa [coefficient2, Complex.sq_norm, Complex.normSq_apply] using h

/-- The full mixed-cubic supplier for arbitrary complex two-level displacement entries. -/
theorem coordinate_mixed_cubic_bound (a b u v r s : ℝ) (w z : ℂ)
    (ha : 0 < a) (hb : 0 < b)
    (kp : (1+hermitian r s z).PosSemidef)
    (kn : (1-hermitian r s z).PosSemidef) :
    |3*(Matrix.trace ((hermitian u v w)^3)).re -
      3*coefficient3 (hermitian a b 0)
        (hermitian u v w + weightedImage a b
          (2*(a^2+a*b+b^2)/(3*(a+b))) (hermitian r s z)) (hermitian r s z)| ≤
      3*coefficient2 (hermitian a b 0)
        (hermitian u v w + weightedImage a b
          (2*(a^2+a*b+b^2)/(3*(a+b))) (hermitian r s z)) (hermitian r s z) := by
  have hab : a+b ≠ 0 := ne_of_gt (add_pos ha hb)
  have hN := mixedMatrix_posSemidef a b u v w z ha hb
  have hp := trace_mul_nonneg_of_posSemidef kp hN
  have hn := trace_mul_nonneg_of_posSemidef kn hN
  change 0 ≤ ((1+hermitian r s z)*mixedMatrix a b u v w z).trace.re at hp
  change 0 ≤ ((1-hermitian r s z)*mixedMatrix a b u v w z).trace.re at hn
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_add,
    Matrix.trace_sub, Complex.add_re, Complex.sub_re] at hp hn
  have hbound : |(Matrix.trace (hermitian r s z*mixedMatrix a b u v w z)).re| ≤
      (Matrix.trace (mixedMatrix a b u v w z)).re :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hmixed := congrArg Complex.re (mixed_identity_complex a b u v r s w z hab)
  have hmass : Matrix.trace (mixedMatrix a b u v w z) =
      3*traceCoefficient2 (hermitian a b 0)
        (hermitian u v w + weightedImage a b
          (2*(a^2+a*b+b^2)/(3*(a+b))) (hermitian r s z)) (hermitian r s z) := by
    rw [mass_identity_complex a b u v w z hab,
      energy_identity_complex a b u v r s w z hab]
    push_cast
    have habC : (a : ℂ)+(b : ℂ) ≠ 0 := by exact_mod_cast hab
    field_simp [habC]
    ring
  rw [hmass] at hbound
  rw [← hmixed] at hbound
  simpa [coefficient2, coefficient3, Complex.mul_re, Complex.sub_re] using
    hbound

/-- Only the K endpoints are needed for the mixed part. The displacement H is arbitrary
Hermitian, and the two positive spectral levels need not be distinct. -/
theorem mixed_cubic_bound (a b : ℝ) (H K : Mat)
    (ha : 0 < a) (hb : 0 < b) (hH : H.IsHermitian) (hK : K.IsHermitian)
    (kp : (1+K).PosSemidef) (kn : (1-K).PosSemidef) :
    |3*(Matrix.trace ((H-weightedImage a b
        (2*(a^2+a*b+b^2)/(3*(a+b))) K)^3)).re -
      3*coefficient3 (hermitian a b 0) H K| ≤
      3*coefficient2 (hermitian a b 0) H K := by
  let m := 2*(a^2+a*b+b^2)/(3*(a+b))
  let L := H-weightedImage a b m K
  have hKrep := hermitian_eq K hK
  have hM : (weightedImage a b m K).IsHermitian := by
    rw [hKrep, weightedImage_hermitian]
    exact hermitian_isHermitian _ _ _
  have hL := hH.sub hM
  have hLrep := hermitian_eq L hL
  have hHrep : H = hermitian (L 0 0).re (L 1 1).re (L 0 1) +
      weightedImage a b m K := by
    rw [← hLrep]
    dsimp [L]
    abel
  change |3*(Matrix.trace (L^3)).re-3*coefficient3 (hermitian a b 0) H K| ≤
    3*coefficient2 (hermitian a b 0) H K
  have h := coordinate_mixed_cubic_bound a b (L 0 0).re (L 1 1).re
    (K 0 0).re (K 1 1).re (L 0 1) (K 0 1) ha hb
    (by simpa only [← hKrep] using kp) (by simpa only [← hKrep] using kn)
  rw [← hLrep, ← hKrep] at h
  change |3*(Matrix.trace (L^3)).re -
    3*coefficient3 (hermitian a b 0) (L+weightedImage a b m K) K| ≤
    3*coefficient2 (hermitian a b 0) (L+weightedImage a b m K) K at h
  have hLH : L+weightedImage a b m K = H := by dsimp [L]; abel
  simpa only [hLH] using h

/-- The real energy identity for arbitrary Hermitian H and K. -/
theorem energy_identity (a b : ℝ) (H K : Mat) (hab : a+b ≠ 0)
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    coefficient2 (hermitian a b 0) H K =
      3*(Matrix.trace (hermitian a b 0*(H-weightedImage a b
        (2*(a^2+a*b+b^2)/(3*(a+b))) K)^2)).re +
      ((a-b)^2*(a^2+3*a*b+b^2)/(3*(a+b)))*‖K 0 1‖^2 := by
  let m := 2*(a^2+a*b+b^2)/(3*(a+b))
  let L := H-weightedImage a b m K
  have hKrep := hermitian_eq K hK
  have hM : (weightedImage a b m K).IsHermitian := by
    rw [hKrep, weightedImage_hermitian]
    exact hermitian_isHermitian _ _ _
  have hL := hH.sub hM
  have hLrep := hermitian_eq L hL
  have h := coordinate_energy_identity a b (L 0 0).re (L 1 1).re
    (K 0 0).re (K 1 1).re (L 0 1) (K 0 1) hab
  rw [← hLrep, ← hKrep] at h
  have hLH : L+weightedImage a b m K = H := by dsimp [L]; abel
  change coefficient2 (hermitian a b 0) (L+weightedImage a b m K) K =
    3*(Matrix.trace (hermitian a b 0*L^2)).re +
      ((a-b)^2*(a^2+3*a*b+b^2)/(3*(a+b)))*‖K 0 1‖^2 at h
  simpa only [hLH] using h

/-- Complete coefficient compatibility for two positive spectral levels and
all original complex Hermitian endpoint constraints. No trace or saturation
restriction is added. The analytic identification with physical derivatives
is not part of this coefficient theorem. -/
theorem coefficient_compatibility (a b : ℝ) (H K : Mat)
    (ha : 0 < a) (hb : 0 < b) (hH : H.IsHermitian) (hK : K.IsHermitian)
    (hp : (hermitian a b 0+H).PosSemidef)
    (hn : (hermitian a b 0-H).PosSemidef)
    (kp : (1+K).PosSemidef) (kn : (1-K).PosSemidef) :
    0 ≤ coefficient2 (hermitian a b 0) H K ∧
      3*|coefficient3 (hermitian a b 0) H K| ≤
        5*coefficient2 (hermitian a b 0) H K := by
  let m := HsfQubitCoupledScalar.mean a b
  let L := H-weightedImage a b m K
  let P := coefficient2 (hermitian a b 0) H K
  let Q := coefficient3 (hermitian a b 0) H K
  let V := (Matrix.trace (hermitian a b 0*L^2)).re
  let U := (Matrix.trace (L^3)).re
  let b0 := (a-b)^2*(a^2+3*a*b+b^2)/(3*(a+b))
  have hab : a+b ≠ 0 := ne_of_gt (add_pos ha hb)
  have hmixed := mixed_cubic_bound a b H K ha hb hH hK kp kn
  change |3*U-3*Q| ≤ 3*P at hmixed
  have hP : 0 ≤ P := by nlinarith [abs_nonneg (3*U-3*Q)]
  have hpure := coupled_cubic_compatibility a b H K ha hb hH hK hp hn kp kn
  change |U| ≤ 2*V+HsfQubitCoupledScalar.penalty a b*‖K 0 1‖^2 at hpure
  have hE := energy_identity a b H K hab hH hK
  change P = 3*V+b0*‖K 0 1‖^2 at hE
  have hpen : HsfQubitCoupledScalar.penalty a b = (2/3)*b0 := by
    dsimp [HsfQubitCoupledScalar.penalty, b0]
    field_simp [hab]
    ring
  have htri := abs_sub (3*U) (3*U-3*Q)
  have hleft : |3*U-(3*U-3*Q)| = 3*|Q| := by
    have heq : 3*U-(3*U-3*Q) = 3*Q := by ring
    rw [heq, abs_mul]
    norm_num
  have hright : |3*U| = 3*|U| := by rw [abs_mul]; norm_num
  rw [hleft, hright] at htri
  rw [hpen] at hpure
  exact ⟨hP, by nlinarith only [htri, hpure, hmixed, hE]⟩

#print axioms mixed_cubic_bound
#print axioms coefficient_compatibility

end D5.S3.Quantum.Matrix.HsfQubitMixedCubic
