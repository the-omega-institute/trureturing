/- GID: D5/S3/Quantum/Matrix/HsfQubitCoupledCubic
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfQubitCoupledCubic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.PosDef]
   utility: none
   digest: Coupled endpoint estimates for complex Hermitian two by two cubic traces. -/

/-
admission_basis: escape-witness
proof_shape: coupled_cubic_compatibility: content
escape_witness: HsfQubitCoupledScalar.coupled_cubic_le
The endpoint, coordinate and trace helpers are bind-only and consumed by
coupled_cubic_compatibility; hermitian_isHermitian, hermitian_eq and
weightedImage_hermitian are also consumed by the
same-delivery HsfQubitMixedCubic supplier. No novelty or full HSF claim.
-/

module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic
public import D5.S3.Quantum.Matrix.HsfQubitCoupledScalar

/-! Endpoint coupling and trace identities for the two dimensional HSF cubic supplier.
The arbitrary-dimensional and general second-variable HSF conjectures remain open. -/

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

private theorem hermitian_neg (a b : ℝ) (z : ℂ) :
    -hermitian a b z = hermitian (-a) (-b) (-z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermitian]

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
