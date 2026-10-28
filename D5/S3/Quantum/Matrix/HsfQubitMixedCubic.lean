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
escape_witness: HsfQubitCoupledCubic.coupled_cubic_compatibility
The six-row mixed certificate is derived from the original ordered trace-word
coefficients. Its endpoint bound requires only the K constraints. Coordinate
and energy helpers are consumed by the final coefficient compatibility theorem.
The analytic derivative identification is a separate obligation; full HSF is open.
-/

module

public import D5.S3.Quantum.Matrix.HsfQubitCoupledCubic
public import D5.S3.Weil.ZetaLinear.RankTrace

/-! The original ordered trace-word coefficients are defined independently of
the six-square certificate. The identities below derive the certificate from
those coefficients. Identification with derivatives of the physical matrix
power function is a separate analytic obligation. Full HSF remains open. -/

@[expose] public section
noncomputable section
open Matrix
open scoped ComplexOrder

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

end Coefficients

private def f (a b : ℝ) : ℝ := 2*(a+2*b)/(3*(a+b))
private def q (a b : ℝ) : ℝ := -(a-b)*(3*a^2+9*a*b+8*b^2)/(18*(a+b)^2)
private def c (a b : ℝ) : ℝ := (a-b)^2*(2*a+3*b)/(a+b)^2
private def j (a b : ℝ) : ℝ := b^2/(3*(a+b))
private def d (a b : ℝ) : ℝ :=
  (a-b)^2*(a+2*b)*(7*a^2+14*a*b+4*b^2)/(36*(a+b)^2)

private def rowGram (x y : ℂ) : Mat :=
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
  unfold mixedMatrix
  exact (((((rowGram_psd _ _).smul (show 0 ≤ 9*a by positivity)).add
    ((rowGram_psd _ _).smul (hc a b ha hb))).add
    ((rowGram_psd _ _).smul (hd a b ha hb))).add
    ((rowGram_psd _ _).smul (show 0 ≤ 9*b by positivity))).add
    ((rowGram_psd _ _).smul (hc b a hb ha))).add
    ((rowGram_psd _ _).smul (hd b a hb ha))

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

private theorem mixed_identity_complex (a b u v r s : ℝ) (w z : ℂ)
    (hab : a+b ≠ 0) :
    3*Matrix.trace ((hermitian u v w)^3) -
      3*traceCoefficient3 (hermitian a b 0)
      (hermitian u v w + weightedImage a b
        (2*(a^2+a*b+b^2)/(3*(a+b))) (hermitian r s z)) (hermitian r s z) =
      Matrix.trace (hermitian r s z*mixedMatrix a b u v w z) := by
  have habC : (a : ℂ)+(b : ℂ) ≠ 0 := by exact_mod_cast hab
  simp [traceCoefficient3, hermitian, weightedImage, mixedMatrix, rowGram,
    Matrix.trace, Matrix.mul_apply, Matrix.vecMulVec, Fin.sum_univ_two,
    Matrix.smul_apply, Complex.real_smul, f, q, c, j, d, pow_succ]
  push_cast
  field_simp [habC]
  ring

private theorem mass_identity_complex (a b u v : ℝ) (w z : ℂ)
    (hab : a+b ≠ 0) :
    Matrix.trace (mixedMatrix a b u v w z) =
      9*Matrix.trace (hermitian a b 0*(hermitian u v w)^2) +
      (((a-b)^2*(a^2+3*a*b+b^2)/(a+b) : ℝ) : ℂ)*(star z*z) := by
  have habC : (a : ℂ)+(b : ℂ) ≠ 0 := by exact_mod_cast hab
  simp [hermitian, mixedMatrix, rowGram, Matrix.trace, Matrix.mul_apply,
    Matrix.vecMulVec, Fin.sum_univ_two, Matrix.smul_apply, Complex.real_smul,
    f, q, c, j, d, pow_succ]
  push_cast
  field_simp [habC]
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
  simpa [coefficient2, Complex.mul_re, Complex.sq_norm, Complex.normSq_apply] using h

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
  have hp := RHLinalg.trace_mul_nonneg_of_posSemidef kp hN
  have hn := RHLinalg.trace_mul_nonneg_of_posSemidef kn hN
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
    ring
  rw [hmass] at hbound
  simpa [coefficient2, coefficient3, Complex.mul_re, Complex.sub_re] using
    (hmixed.symm ▸ hbound)

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
