/- GID: D5/S3/Quantum/Matrix/AbedNikolaevaNovikovItemSix
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/AbedNikolaevaNovikovItemSix
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The sharp spectral-mean trace-violation envelope for faithful complex qubit densities. -/

/-
admission_basis: open-problem-resolution (#22896; Proved)
escape_witness: none
proof_shape: result: bind-only; settling result of the external named open problem.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24453.
The literal spectral contrast occurs in envelope; proofs use the existing
AbedNikolaevaNovikovTwoContrastYoung.contrast, with definitional correspondence.
The real trace functional is bornProbability followed by Complex.re.
Direct frozen dependencies: see the per-declaration inventory below.
-/

import D5.S3.Quantum.Matrix.SpectralGeometricLogEuclideanRefutation
import D5.S3.Quantum.Matrix.SpectralPower
import D5.S3.Quantum.Matrix.AlternativeMeanLinearization
import D5.S3.Quantum.Matrix.CartesianVariance
import D5.S3.Quantum.Matrix.AbedNikolaevaNovikovTwoContrastYoung
import D5.S3.Quantum.Matrix.AbedNikolaevaNovikovAFDensityBound
import D5.S3.Quantum.FiniteDimensional
import D5.S3.Quantum.Bogoliubov.HardyBlockConservation
import D5.S3.Quantum.BlockNorm.EssentiallyHermitian
import D5.S3.TotalVariation.Hellinger
import Mathlib.Analysis.Matrix.Spectrum

set_option maxHeartbeats 800000

noncomputable section

namespace D5.S3.Quantum.Matrix.AbedNikolaevaNovikovItemSix

open Filter Topology _root_.Matrix
open scoped ComplexOrder MatrixOrder
open D5.S3.Quantum.FiniteDimensional (bornProbability)
open D5.S3.Quantum.Matrix.SpectralGeometricLogEuclideanRefutation (specMean wgm)
open D5.S3.Quantum.Matrix.SpectralPower (mpow)
open D5.S3.Quantum.Matrix.AlternativeMeanLinearization (gmInv riccati riccati_unique half_eq_sqrt)
open D5.S3.Quantum.Matrix.AbedNikolaevaNovikovTwoContrastYoung (contrast)

/-- The supremum of the relative item-6 trace violation. -/
def V (ρ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  sSup {r : ℝ | ∃ (A B : Matrix (Fin 2) (Fin 2) ℂ), A.PosDef ∧ B.PosDef ∧
    r = ((bornProbability ρ (specMean A B (1 / 2))).re -
      Real.sqrt ((bornProbability ρ A).re * (bornProbability ρ B).re)) /
      Real.sqrt ((bornProbability ρ A).re * (bornProbability ρ B).re)}

/-- The envelope over all faithful complex qubit densities of prescribed contrast. -/
def envelope (δ : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ (ρ : Matrix (Fin 2) (Fin 2) ℂ), ρ.PosDef ∧
    (sSup (spectrum ℝ ρ) - sInf (spectrum ℝ ρ)) /
      (sSup (spectrum ℝ ρ) + sInf (spectrum ℝ ρ)) = δ ∧ r = V ρ}

/-- Conjecture 11.1, item 6, for the faithful range. -/
def claim : Prop :=
  ∀ (δ : ℝ), 0 ≤ δ → δ < 1 → envelope δ = 1 / Real.sqrt (1 - δ ^ 2) - 1

private lemma difference_sq_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x-y)^2 ≤ |x^2-y^2| := by
  have h := D5.S3.TotalVariation.Hellinger.sq_sqrt_sub_sqrt_le_abs_sub (x^2) (y^2)
  rw [Real.sqrt_sq hx, Real.sqrt_sq hy] at h
  exact h


private lemma quadratic_nonneg (t u v : ℝ) (ht : -1 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ u^2+v^2+2*t*u*v := by
  nlinarith [sq_nonneg (u-v), mul_nonneg (by linarith : 0 ≤ 1+t) (mul_nonneg hu hv)]

private theorem scalar_squared (t u v x y : ℝ) (ht : |t| < 1)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (1-t^2)*(u^2*x^2+v^2*y^2+2*t*u*v*x*y)^2 ≤
      (u^2+v^2+2*t*u*v)*(u^2*x^4+v^2*y^4+2*t*u*v*x^2*y^2) := by
  let F := u^2*x^2+v^2*y^2+2*t*u*v*x*y
  let H := u^2*x^2+v^2*y^2+t*u*v*(x^2+y^2)
  let w := u*v*|x^2-y^2|
  let d := u*v*(x-y)^2
  have ht1 : -1 ≤ t := (abs_lt.mp ht).1.le
  have ht2 : 0 ≤ 1-t^2 := sub_nonneg.mpr (((sq_lt_one_iff_abs_lt_one t).mpr ht).le)
  have hF : 0 ≤ F := by
    convert quadratic_nonneg t (u*x) (v*y) ht1
      (mul_nonneg hu hx) (mul_nonneg hv hy) using 1 <;> dsimp [F] <;> ring
  have hd : 0 ≤ d := mul_nonneg (mul_nonneg hu hv) (sq_nonneg _)
  have hdw : d ≤ w := mul_le_mul_of_nonneg_left (difference_sq_le x y hx hy) (mul_nonneg hu hv)
  have hw : 0 ≤ w := le_trans hd hdw
  have he : F = H-t*d := by dsimp [F,H,d]; ring
  have hb : F ≤ H+|t| *w := by
    have h1 := mul_le_mul_of_nonneg_right (neg_le_abs t) hd
    have h2 := mul_le_mul_of_nonneg_left hdw (abs_nonneg t)
    nlinarith only [he,h1,h2]
  have hsq : F^2 ≤ (H+|t| *w)^2 := (sq_le_sq₀ hF (le_trans hF hb)).mpr hb
  have habs : |t|^2 = t^2 := sq_abs t
  have hcs : (1-t^2)*(H+|t| *w)^2 ≤ H^2+(1-t^2)*w^2 := by
    have hi : H^2+(1-t^2)*w^2-(1-t^2)*(H+|t| *w)^2 =
        (|t| *H-(1-t^2)*w)^2 := by
      simp only [add_sq, sub_sq, mul_pow, sq_abs]
      ring
    nlinarith only [sq_nonneg (|t| *H-(1-t^2)*w),hi]
  have hid : H^2+(1-t^2)*w^2 =
      (u^2+v^2+2*t*u*v)*(u^2*x^4+v^2*y^4+2*t*u*v*x^2*y^2) := by
    dsimp [H,w]
    rw [mul_pow, mul_pow, sq_abs]
    ring
  exact (mul_le_mul_of_nonneg_left hsq ht2).trans (hcs.trans_eq hid)


private lemma mpow_inv {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosDef) (p : ℝ) :
    mpow A⁻¹ p = mpow A (-p) := by
  unfold mpow
  rw [← CFC.rpow_eq_cfc_real hA.inv.posSemidef.nonneg,
    Matrix.nonsing_inv_eq_ringInverse,
    CFC.inverse_eq_rpow_neg_one hA.isStrictlyPositive,
    CFC.rpow_rpow A (-1) p (by norm_num) hA.isStrictlyPositive,
    CFC.rpow_eq_cfc_real hA.posSemidef.nonneg]
  congr 1
  funext t
  congr 1
  ring

private lemma mpow_half {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosDef) :
    mpow A (1/2) = CFC.sqrt A := by
  exact half_eq_sqrt hA

private lemma wgm_inverse {A B : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosDef) :
    wgm A⁻¹ B (1/2) = gmInv A B := by
  unfold wgm
  rw [mpow_inv hA,mpow_inv hA]
  norm_num only [neg_div,neg_neg] 
  rfl

private theorem spectral_param {A B : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    ∃ X : Matrix (Fin 2) (Fin 2) ℂ, X.PosDef ∧ B = (X*X)*A*(X*X) ∧
      specMean A B (1/2) = X*A*X := by
  let P := wgm A⁻¹ B (1/2)
  have hP : P.PosDef := by rw [show P = gmInv A B from wgm_inverse hA]; exact (riccati hA hB).1
  let X := CFC.sqrt P
  have hX : X.PosDef := hP.isStrictlyPositive.sqrt.posDef
  have hXX : X*X = P := CFC.sqrt_mul_sqrt_self P hP.posSemidef.nonneg
  refine ⟨X,hX,?_,?_⟩
  · rw [hXX,show P = gmInv A B from wgm_inverse hA]
    exact (riccati hA hB).2.symm
  · change mpow P (1/2)*A*mpow P (1/2) = X*A*X
    rw [mpow_half hP]

private theorem spectral_congruence {A X : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosDef) (hX : X.PosDef) :
    specMean A ((X*X)*A*(X*X)) (1/2) = X*A*X := by
  have hXX : (X*X).PosDef := by
    simpa only [pow_two] using
      (hX.posSemidef.pow 2).posDef_iff_isUnit.mpr (hX.isUnit.pow 2)
  have hP : wgm A⁻¹ ((X*X)*A*(X*X)) (1/2) = X*X := by
    rw [wgm_inverse hA]
    exact riccati_unique hA hXX rfl
  unfold specMean
  rw [hP,mpow_half hXX,CFC.sqrt_mul_self X hX.posSemidef.nonneg]


private theorem spectrum_pair {R : Matrix (Fin 2) (Fin 2) ℂ} (hR : R.IsHermitian) :
    spectrum ℝ R = {hR.eigenvalues 0,hR.eigenvalues 1} := by
  rw [hR.spectrum_real_eq_range_eigenvalues]
  ext x
  simp only [Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩

private theorem contrast_invariants {R : Matrix (Fin 2) (Fin 2) ℂ} (hR : R.PosDef) :
    0 ≤ contrast R ∧ contrast R < 1 ∧
      (1-(contrast R)^2)*(R.trace.re)^2 = 4*R.det.re := by
  let a := hR.isHermitian.eigenvalues 0
  let b := hR.isHermitian.eigenvalues 1
  have ha : 0 < a := hR.eigenvalues_pos 0
  have hb : 0 < b := hR.eigenvalues_pos 1
  have hm : sInf (spectrum ℝ R) = min a b := by
    rw [spectrum_pair hR.isHermitian,csInf_pair]
  have hM : sSup (spectrum ℝ R) = max a b := by
    rw [spectrum_pair hR.isHermitian,csSup_pair]
  have ht : R.trace.re = a+b := by
    simpa [Fin.sum_univ_two,a,b] using congrArg Complex.re hR.isHermitian.trace_eq_sum_eigenvalues
  have hd : R.det.re = a*b := by
    simpa [Fin.prod_univ_two,a,b] using congrArg Complex.re hR.isHermitian.det_eq_prod_eigenvalues
  have hmin : 0 < min a b := lt_min ha hb
  have hmax : 0 < max a b := lt_max_of_lt_left ha
  have hs : 0 < max a b+min a b := add_pos hmax hmin
  have hc : contrast R = (max a b-min a b)/(max a b+min a b) := by
    rw [contrast,hm,hM]
  refine ⟨?_,?_,?_⟩
  · rw [hc]
    exact div_nonneg (sub_nonneg.mpr (min_le_max)) hs.le
  · rw [hc,div_lt_one hs]
    linarith
  · rw [hc,ht,hd]
    have hsum : max a b+min a b = a+b := max_add_min a b
    have hprod : min a b*max a b = a*b := min_mul_max a b
    rw [← hsum,← hprod]
    field_simp [hs.ne']
    <;> ring


private theorem phi_diagonal {R A : Matrix (Fin 2) (Fin 2) ℂ} (hR : R.PosDef) (hA : A.PosDef) (x y : ℝ) :
    (bornProbability R (diagonal ![(x : ℂ),(y : ℂ)]*A*diagonal ![(x : ℂ),(y : ℂ)])).re =
      (R 0 0).re*(A 0 0).re*x^2+(R 1 1).re*(A 1 1).re*y^2+
        2*(R 0 1*A 1 0).re*x*y := by
  have hR00 := (Complex.pos_iff.mp (hR.diag_pos (i := 0))).2.symm
  have hR11 := (Complex.pos_iff.mp (hR.diag_pos (i := 1))).2.symm
  have hA00 := (Complex.pos_iff.mp (hA.diag_pos (i := 0))).2.symm
  have hA11 := (Complex.pos_iff.mp (hA.diag_pos (i := 1))).2.symm
  have hR10 : R 1 0 = star (R 0 1) := (hR.isHermitian.apply 1 0).symm
  have hA01 : A 0 1 = star (A 1 0) := (hA.isHermitian.apply 0 1).symm
  simp [D5.S3.Quantum.FiniteDimensional.bornProbability,
    Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two,Matrix.diagonal,
    hR10,hA01,Complex.mul_re,Complex.mul_im,hR00,hR11,hA00,hA11]
  <;> ring

private theorem offdiag_contrast {R : Matrix (Fin 2) (Fin 2) ℂ} (hR : R.PosDef) (δ : ℝ)
    (hinv : (1-δ^2)*R.trace.re^2 = 4*R.det.re) :
    Complex.normSq (R 0 1) ≤ δ^2*(R 0 0).re*(R 1 1).re := by
  have h0 := (Complex.pos_iff.mp (hR.diag_pos (i := 0))).1
  have h1 := (Complex.pos_iff.mp (hR.diag_pos (i := 1))).1
  have him0 := (Complex.pos_iff.mp (hR.diag_pos (i := 0))).2.symm
  have him1 := (Complex.pos_iff.mp (hR.diag_pos (i := 1))).2.symm
  have hstar := hR.isHermitian.apply 1 0
  have hdet : R.det.re = (R 0 0).re*(R 1 1).re-Complex.normSq (R 0 1) := by
    rw [det_fin_two,← hstar]
    simp [Complex.mul_re,Complex.normSq_apply,him0,him1]
    <;> ring
  have htrace : R.trace.re = (R 0 0).re+(R 1 1).re := by
    simpa only [Complex.add_re] using congrArg Complex.re (Matrix.trace_fin_two R)
  have hpsd := D5.S3.Quantum.Matrix.CartesianVariance.psd_entry_bound hR.posSemidef 0 1
  have hid : (δ^2*(R 0 0).re*(R 1 1).re-Complex.normSq (R 0 1))*
      ((R 0 0).re+(R 1 1).re)^2 =
      ((R 0 0).re-(R 1 1).re)^2*((R 0 0).re*(R 1 1).re-Complex.normSq (R 0 1)) := by
    rw [htrace,hdet] at hinv
    have hm := congrArg (fun z : ℝ => z*((R 0 0).re*(R 1 1).re)) hinv
    nlinarith only [hm]
  have hr := mul_nonneg (sq_nonneg ((R 0 0).re-(R 1 1).re)) (sub_nonneg.mpr hpsd)
  have hs : 0 < ((R 0 0).re+(R 1 1).re)^2 := sq_pos_of_pos (add_pos h0 h1)
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hs).mp (hid.symm ▸ hr))

private theorem diagonal_trace_bound {R A : Matrix (Fin 2) (Fin 2) ℂ} (hR : R.PosDef) (hA : A.PosDef)
    (δ x y : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ < 1) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hinv : (1-δ^2)*R.trace.re^2 = 4*R.det.re) :
    (let D : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![(x : ℂ),(y : ℂ)]
     (1-δ^2)*((bornProbability R (D*A*D)).re)^2 ≤ (bornProbability R A).re * (bornProbability R ((D*D)*A*(D*D))).re) := by
  dsimp only
  let a := (R 0 0).re
  let b := (R 1 1).re
  let p := (A 0 0).re
  let q := (A 1 1).re
  let c := (R 0 1*A 1 0).re
  let u := Real.sqrt (a*p)
  let v := Real.sqrt (b*q)
  let t := c/(u*v)
  have ha : 0 < a := (Complex.pos_iff.mp (hR.diag_pos (i := 0))).1
  have hb : 0 < b := (Complex.pos_iff.mp (hR.diag_pos (i := 1))).1
  have hp : 0 < p := (Complex.pos_iff.mp (hA.diag_pos (i := 0))).1
  have hq : 0 < q := (Complex.pos_iff.mp (hA.diag_pos (i := 1))).1
  have hu : 0 < u := Real.sqrt_pos.mpr (mul_pos ha hp)
  have hv : 0 < v := Real.sqrt_pos.mpr (mul_pos hb hq)
  have hu2 : u^2=a*p := Real.sq_sqrt (mul_pos ha hp).le
  have hv2 : v^2=b*q := Real.sq_sqrt (mul_pos hb hq).le
  have hcn : c^2 ≤ Complex.normSq (R 0 1)*Complex.normSq (A 1 0) := by
    simpa only [Complex.normSq_mul, pow_two] using Complex.re_sq_le_normSq (R 0 1*A 1 0)
  have hRentry := offdiag_contrast hR δ hinv
  have hAentry := D5.S3.Quantum.Matrix.CartesianVariance.psd_entry_bound hA.posSemidef 1 0
  have hc : c^2 ≤ δ^2*(u*v)^2 := by
    calc
      c^2 ≤ Complex.normSq (R 0 1)*Complex.normSq (A 1 0) := hcn
      _ ≤ (δ^2*a*b)*(q*p) :=
        mul_le_mul hRentry hAentry (Complex.normSq_nonneg _) (by positivity)
      _ = δ^2*(u*v)^2 := by rw [mul_pow,hu2,hv2]; ring
  have huv : 0 < u*v := mul_pos hu hv
  have htc : t*(u*v)=c := div_mul_cancel₀ c huv.ne'
  have ht2 : t^2 ≤ δ^2 := by
    apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos huv)).mp
    calc
      t^2*(u*v)^2 = c^2 := by rw [← mul_pow,htc]
      _ ≤ δ^2*(u*v)^2 := hc
  have htd : |t| ≤ δ := abs_le_of_sq_le_sq ht2 hδ
  have hscalar := scalar_squared t u v x y (htd.trans_lt hδ1) hu.le hv.le hx hy
  have hδt : 0 ≤ δ^2-t^2 := sub_nonneg.mpr ht2
  have hmain :
      (1-δ^2)*(u^2*x^2+v^2*y^2+2*t*u*v*x*y)^2 ≤
      (u^2+v^2+2*t*u*v)*(u^2*x^4+v^2*y^4+2*t*u*v*x^2*y^2) := by
    have hh := mul_nonneg hδt (sq_nonneg (u^2*x^2+v^2*y^2+2*t*u*v*x*y))
    nlinarith only [hh,hscalar]
  have hD2 : (diagonal ![(x : ℂ),(y : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ)*diagonal ![(x : ℂ),(y : ℂ)] =
      diagonal ![((x^2 : ℝ) : ℂ),((y^2 : ℝ) : ℂ)] := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [pow_two]
  have h0 := phi_diagonal hR hA 1 1
  have h2 := phi_diagonal hR hA x y
  have h4 := phi_diagonal hR hA (x^2) (y^2)
  have hcone : (diagonal ![(1 : ℂ),1] : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by ext i j; fin_cases i <;> fin_cases j <;> simp
  simp only [Complex.ofReal_one] at h0
  rw [hcone,one_mul,mul_one] at h0
  change (bornProbability R A).re = a*p*1^2+b*q*1^2+2*c*1*1 at h0
  change (bornProbability R _).re = a*p*x^2+b*q*y^2+2*c*x*y at h2
  change (bornProbability R _).re = a*p*(x^2)^2+b*q*(y^2)^2+2*c*x^2*y^2 at h4
  have hc0 : 2*t*u*v = 2*c := by nlinarith only [htc]
  rw [mul_pow,hu2,hv2] at hc
  rw [hu2,hv2,hc0] at hmain
  simp only [one_pow,mul_one] at h0
  rw [hD2,h0,h2,h4]
  convert hmain using 1 <;> ring

private theorem trace_bound {R A X : Matrix (Fin 2) (Fin 2) ℂ} (hR : R.PosDef) (hA : A.PosDef) (hX : X.PosDef)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (hinv : (1-δ^2)*R.trace.re^2=4*R.det.re) :
    (1-δ^2)*((bornProbability R (X*A*X)).re)^2 ≤ (bornProbability R A).re*(bornProbability R ((X*X)*A*(X*X))).re := by
  let U := hX.isHermitian.eigenvectorUnitary
  let e := Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) (star U)
  have he_apply (Y : Matrix (Fin 2) (Fin 2) ℂ) : e Y=star (U : Matrix (Fin 2) (Fin 2) ℂ)*Y*(U : Matrix (Fin 2) (Fin 2) ℂ) := by
    simpa only [e,Unitary.coe_star] using
      (Unitary.conjStarAlgAut_star_apply (S := ℂ) U Y)
  have hRe : (e R).PosDef := by
    rw [he_apply]
    simpa only [star_eq_conjTranspose] using
      (Unitary.isUnit_coe (U := U)).posDef_star_left_conjugate_iff.mpr hR
  have hAe : (e A).PosDef := by
    rw [he_apply]
    simpa only [star_eq_conjTranspose] using
      (Unitary.isUnit_coe (U := U)).posDef_star_left_conjugate_iff.mpr hA
  have htrace (Y : Matrix (Fin 2) (Fin 2) ℂ) : (e Y).trace=Y.trace := by
    rw [he_apply]
    exact Matrix.trace_units_conj' (Unitary.toUnits U) Y
  have hphi (Y : Matrix (Fin 2) (Fin 2) ℂ) : (bornProbability (e R) (e Y)).re=(bornProbability R Y).re := by
    change ((e R*e Y).trace).re=(R*Y).trace.re
    rw [← map_mul,htrace]
  have hdet : (e R).det=R.det := by
    rw [he_apply]
    exact Matrix.det_units_conj' (Unitary.toUnits U) R
  have hinve : (1-δ^2)*(e R).trace.re^2=4*(e R).det.re := by
    rw [htrace,hdet]; exact hinv
  have hd : e X=diagonal ![((hX.isHermitian.eigenvalues 0) : ℂ),((hX.isHermitian.eigenvalues 1) : ℂ)] := by
    convert hX.isHermitian.conjStarAlgAut_star_eigenvectorUnitary using 1
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hb := diagonal_trace_bound hRe hAe δ (hX.isHermitian.eigenvalues 0)
    (hX.isHermitian.eigenvalues 1) hδ hδ1 (hX.eigenvalues_pos 0).le (hX.eigenvalues_pos 1).le hinve
  dsimp only at hb
  rw [← hd] at hb
  simpa only [← map_mul,hphi] using hb

private theorem phi_pos {R A : Matrix (Fin 2) (Fin 2) ℂ} (hR : R.PosDef) (hA : A.PosDef) : 0 < (bornProbability R A).re := by
  exact D5.S3.Quantum.Matrix.AbedNikolaevaNovikovAFDensityBound.trace_pair_pos
    R A hR hA.posSemidef hA.isUnit.ne_zero


private theorem quotient_bound {R A B : Matrix (Fin 2) (Fin 2) ℂ} (hR : R.PosDef) (hA : A.PosDef) (hB : B.PosDef) :
    ((bornProbability R (specMean A B (1/2))).re-Real.sqrt ((bornProbability R A).re*(bornProbability R B).re))/Real.sqrt ((bornProbability R A).re*(bornProbability R B).re) ≤
      1/Real.sqrt (1-(contrast R)^2)-1 := by
  obtain ⟨X,hX,hBXX,hS⟩ := spectral_param hA hB
  have hδ := contrast_invariants hR
  have hs := trace_bound hR hA hX (contrast R) hδ.1 hδ.2.1 hδ.2.2
  rw [← hBXX,← hS] at hs
  have hSpos : (specMean A B (1/2)).PosDef := by
    rw [hS]
    simpa only [star_eq_conjTranspose,hX.isHermitian.eq] using
      hX.isUnit.posDef_star_right_conjugate_iff.mpr hA
  have hnum : 0 < (bornProbability R (specMean A B (1/2))).re := phi_pos hR hSpos
  have hApos := phi_pos hR hA
  have hBpos := phi_pos hR hB
  have hd : 0 < 1-(contrast R)^2 := sub_pos.mpr ((sq_lt_one_iff₀ hδ.1).mpr hδ.2.1)
  have hsd : 0 < Real.sqrt (1-(contrast R)^2) := Real.sqrt_pos.mpr hd
  have hsp : 0 < Real.sqrt ((bornProbability R A).re*(bornProbability R B).re) := Real.sqrt_pos.mpr (mul_pos hApos hBpos)
  have hsq : (Real.sqrt (1-(contrast R)^2)*(bornProbability R (specMean A B (1/2))).re)^2 ≤
      (Real.sqrt ((bornProbability R A).re*(bornProbability R B).re))^2 := by
    rw [mul_pow,Real.sq_sqrt hd.le,Real.sq_sqrt (mul_pos hApos hBpos).le]
    exact hs
  have hlin := (sq_le_sq₀ (mul_pos hsd hnum).le hsp.le).mp hsq
  have hratio : (bornProbability R (specMean A B (1/2))).re/Real.sqrt ((bornProbability R A).re*(bornProbability R B).re) ≤
      1/Real.sqrt (1-(contrast R)^2) := by
    apply (div_le_div_iff₀ hsp hsd).mpr
    simpa only [one_mul,mul_comm] using hlin
  rw [sub_div,div_self hsp.ne']
  linarith only [hratio]

private theorem V_bound {R : Matrix (Fin 2) (Fin 2) ℂ} (hR : R.PosDef) :
    V R ≤ 1/Real.sqrt (1-(contrast R)^2)-1 := by
  apply csSup_le
  · exact ⟨_,1,1,Matrix.PosDef.one,Matrix.PosDef.one,rfl⟩
  · rintro r ⟨A,B,hA,hB,rfl⟩
    exact quotient_bound hR hA hB

private def density (δ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![(1 : ℂ),(-δ : ℝ);(-δ : ℝ),1]
private def sharpA (δ ε : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![((1+ε : ℝ) : ℂ),(δ : ℂ);(δ : ℂ),((δ^2+ε : ℝ) : ℂ)]
private def sharpX (ε : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![(1 : ℂ),(ε : ℂ)]
private def sharpB (δ ε : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  D5.S3.Quantum.Bogoliubov.HardyBlockConservation.compressedBlock
    (sharpX ε*sharpX ε) (sharpA δ ε)
private def f0 (δ ε : ℝ) : ℝ := 1-δ^2+2*ε
private def f2 (δ ε : ℝ) : ℝ := 1+ε+(δ^2+ε)*ε^2-2*δ^2*ε
private def f4 (δ ε : ℝ) : ℝ := 1+ε+(δ^2+ε)*ε^4-2*δ^2*ε^2
private def familyRatio (δ ε : ℝ) : ℝ := (f2 δ ε-Real.sqrt (f0 δ ε*f4 δ ε))/Real.sqrt (f0 δ ε*f4 δ ε)

private theorem density_data (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    (density δ).PosDef ∧ contrast (density δ)=δ := by
  have hd : 0 < 1-δ^2 := sub_pos.mpr ((sq_lt_one_iff₀ hδ).mpr hδ1)
  have hR : (density δ).PosDef := by
    apply D5.S3.Quantum.Matrix.SpectralPower.posDef_two 1 (-δ) 1 (by norm_num)
    nlinarith only [hd]
  have hi := contrast_invariants hR
  have ht : (density δ).trace.re=2 := by norm_num [density,Matrix.trace,Fin.sum_univ_two]
  have hdet : (density δ).det.re=1-δ^2 := by norm_num [density,Matrix.det_fin_two,Complex.mul_re] <;> ring
  have hs : contrast (density δ)^2=δ^2 := by rw [ht,hdet] at hi; nlinarith only [hi.2.2]
  exact ⟨hR,(sq_eq_sq₀ hi.1 hδ).mp hs⟩

private theorem sharp_positive (δ ε : ℝ) (hε : 0 < ε) :
    (sharpA δ ε).PosDef ∧ (sharpX ε).PosDef ∧ (sharpB δ ε).PosDef := by
  have hA : (sharpA δ ε).PosDef := by
    apply D5.S3.Quantum.Matrix.SpectralPower.posDef_two (1+ε) δ (δ^2+ε) (by linarith)
    have hh : 0 < ε*(1+δ^2+ε) := mul_pos hε (by nlinarith [sq_nonneg δ])
    nlinarith only [hh]
  have hX : (sharpX ε).PosDef := by
    apply Matrix.posDef_diagonal_iff.mpr
    intro i
    fin_cases i
    · norm_num
    · change (0 : ℂ) < (ε : ℂ)
      exact_mod_cast hε
  have hXX : (sharpX ε*sharpX ε).PosDef := by
    simpa only [pow_two] using
      (hX.posSemidef.pow 2).posDef_iff_isUnit.mpr (hX.isUnit.pow 2)
  refine ⟨hA,hX,?_⟩
  simpa only [sharpB,D5.S3.Quantum.Bogoliubov.HardyBlockConservation.compressedBlock,star_eq_conjTranspose,hXX.isHermitian.eq] using
    hXX.isUnit.posDef_star_right_conjugate_iff.mpr hA

private theorem sharp_traces (δ ε : ℝ) (hε : 0 < ε) :
    (bornProbability (density δ) (sharpA δ ε)).re=f0 δ ε ∧
    (bornProbability (density δ) (specMean (sharpA δ ε) (sharpB δ ε) (1/2))).re=f2 δ ε ∧
    (bornProbability (density δ) (sharpB δ ε)).re=f4 δ ε := by
  have hp := sharp_positive δ ε hε
  have hm : specMean (sharpA δ ε) (sharpB δ ε) (1/2)=sharpX ε*sharpA δ ε*sharpX ε :=
    spectral_congruence hp.1 hp.2.1
  rw [hm]
  constructor
  · norm_num [D5.S3.Quantum.FiniteDimensional.bornProbability,density,sharpA,f0,
      Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.diagonal,Fin.sum_univ_two,Complex.mul_re,Complex.mul_im,pow_two]
    <;> ring
  constructor
  · norm_num [D5.S3.Quantum.FiniteDimensional.bornProbability,density,sharpA,sharpX,f2,
      Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.diagonal,Fin.sum_univ_two,Complex.mul_re,Complex.mul_im,pow_two]
    <;> ring
  · norm_num [D5.S3.Quantum.FiniteDimensional.bornProbability,density,sharpA,sharpX,sharpB,D5.S3.Quantum.Bogoliubov.HardyBlockConservation.compressedBlock,f4,
      Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.diagonal,Fin.sum_univ_two,Complex.mul_re,Complex.mul_im,pow_two]
    <;> ring

open Filter Topology in
private theorem family_limit (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    Tendsto (familyRatio δ) (𝓝[>] (0 : ℝ)) (𝓝 (1/Real.sqrt (1-δ^2)-1)) := by
  have hd : 0 < 1-δ^2 := sub_pos.mpr ((sq_lt_one_iff₀ hδ).mpr hδ1)
  have hs : 0 < Real.sqrt (1-δ^2) := Real.sqrt_pos.mpr hd
  have hc : ContinuousAt (familyRatio δ) 0 := by
    unfold familyRatio
    apply ContinuousAt.div
    · unfold f0 f2 f4; fun_prop
    · unfold f0 f4; fun_prop
    · simpa [f0,f4] using hs.ne'
  have hvalue : familyRatio δ 0=1/Real.sqrt (1-δ^2)-1 := by
    simp [familyRatio,f0,f2,f4,sub_div,hs.ne']
  rw [← hvalue]
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

private theorem sharp_lower (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    1/Real.sqrt (1-δ^2)-1 ≤ V (density δ) := by
  have hd := density_data δ hδ hδ1
  let Q : Set ℝ := {r : ℝ | ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A.PosDef ∧ B.PosDef ∧
    r=((bornProbability (density δ) (specMean A B (1/2))).re-Real.sqrt ((bornProbability (density δ) A).re*(bornProbability (density δ) B).re))/
      Real.sqrt ((bornProbability (density δ) A).re*(bornProbability (density δ) B).re)}
  have hb : BddAbove Q := by
    refine ⟨1/Real.sqrt (1-δ^2)-1,?_⟩
    rintro r ⟨A,B,hA,hB,rfl⟩
    simpa only [hd.2] using quotient_bound hd.1 hA hB
  have hle (ε : ℝ) (hε : 0 < ε) : familyRatio δ ε ≤ V (density δ) := by
    have hp := sharp_positive δ ε hε
    have ht := sharp_traces δ ε hε
    change familyRatio δ ε ≤ sSup Q
    apply le_csSup hb
    refine ⟨sharpA δ ε,sharpB δ ε,hp.1,hp.2.2,?_⟩
    rw [ht.1,ht.2.1,ht.2.2]
    rfl
  apply le_of_tendsto (family_limit δ hδ hδ1)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hle ε hε


theorem result : claim := by
  intro δ hδ hδ1
  have hd := density_data δ hδ hδ1
  let G := 1/Real.sqrt (1-δ^2)-1
  have hb : ∀ r ∈ {r : ℝ | ∃ R : Matrix (Fin 2) (Fin 2) ℂ, R.PosDef ∧ contrast R=δ ∧ r=V R}, r ≤ G := by
    rintro r ⟨R,hR,hc,rfl⟩
    simpa only [hc] using V_bound hR
  have hm : V (density δ) ∈ {r : ℝ | ∃ R : Matrix (Fin 2) (Fin 2) ℂ, R.PosDef ∧ contrast R=δ ∧ r=V R} :=
    ⟨density δ,hd.1,hd.2,rfl⟩
  apply le_antisymm (csSup_le ⟨_,hm⟩ hb)
  exact (sharp_lower δ hδ hδ1).trans (le_csSup ⟨G,hb⟩ hm)


end D5.S3.Quantum.Matrix.AbedNikolaevaNovikovItemSix
