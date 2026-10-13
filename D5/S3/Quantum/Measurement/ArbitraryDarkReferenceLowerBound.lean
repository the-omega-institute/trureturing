/- GID: D5/S3/Quantum/Measurement/ArbitraryDarkReferenceLowerBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/ArbitraryDarkReferenceLowerBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A common entangled reference test bounds every instrument with a pure dark state. -/

import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace D5.S3.Quantum.Measurement.ArbitraryDarkReferenceLowerBound

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Matrix Kronecker

private abbrev Q := Fin 2
private abbrev O := Bool × Q
private abbrev J := Q × Q
private abbrev JO := Q × O

private def outer {n : Type*} (v : n → ℂ) : Matrix n n ℂ :=
  Matrix.vecMulVec v (star v)

private theorem kraus_pure_column {k : Type*} [Fintype k]
    (K : k → Matrix O Q ℂ)
    (hfixed : (∑ j, K j * Matrix.single (0 : Q) (0 : Q) (1 : ℂ) * (K j)ᴴ) =
      Matrix.single (false, 0) (false, 0) 1)
    (hcomp : (∑ j, (K j)ᴴ * K j) = 1) :
    (∀ j p, K j p 0 = if p = (false, 0) then K j (false, 0) 0 else 0) ∧
      (∑ j, Complex.normSq (K j (false, 0) 0)) = 1 ∧
      (∑ j, star (K j (false, 0) 0) * K j (false, 0) 1) = 0 := by
  have hs (p : O) : (∑ j, Complex.normSq (K j p 0)) =
      if p = (false, 0) then 1 else 0 := by
    have h := congrArg (fun M : Matrix O O ℂ => (M p p).re) hfixed
    simpa [Matrix.sum_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.single, Matrix.conjTranspose_apply, Complex.mul_conj,
      apply_ite, eq_comm] using h
  have hz (j : k) (p : O) (hp : p ≠ (false, 0)) : K j p 0 = 0 := by
    apply Complex.normSq_eq_zero.mp
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      Complex.normSq_nonneg (K j p 0))).mp (by simpa [hp] using hs p)
        j (Finset.mem_univ j)
  have hc (j : k) (p : O) :
      K j p 0 = if p = (false, 0) then K j (false, 0) 0 else 0 := by
    by_cases hp : p = (false, 0)
    · simp [hp]
    · simp [hp, hz j p hp]
  refine ⟨hc, by simpa using hs (false, 0), ?_⟩
  have h := congrArg (fun M : Matrix Q Q ℂ => M 0 1) hcomp
  simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two,
    hz _ (false, 1) (by decide), hz _ (true, 0) (by decide),
    hz _ (true, 1) (by decide)] using h

private theorem projection_test_bound {n : Type*} [Fintype n] [DecidableEq n]
    (D E : Matrix n n ℂ) (hE : Eᴴ = E) (hEE : E * E = E)
    (htrace : Matrix.trace D = 0) :
    -(Matrix.trace (E * D)).re ≤ traceNorm D / 2 := by
  let U : Matrix n n ℂ := 1 - (2 : ℂ) • E
  have hUstar : Uᴴ = U := by simp [U, hE]
  have hUU : U * U = 1 := by
    dsimp [U]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, hEE]
    module
  have hU : U ∈ Matrix.unitaryGroup n ℂ := by
    change star U * U = 1 ∧ U * star U = 1
    simpa only [Matrix.star_eq_conjTranspose, hUstar] using And.intro hUU hUU
  have h := (traceNorm_eq_max_re_tr_U D).2 ⟨⟨U, hU⟩, rfl⟩
  change (Matrix.trace (U * D)).re ≤ traceNorm D at h
  simp only [U, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, htrace,
    Complex.sub_re, Complex.mul_re] at h
  norm_num at h
  linarith

/-- The lower bound obtained from one two-qubit reference input. -/
def referenceLowerBound (a z : ℝ) : ℝ :=
  (Real.sqrt (a ^ 2 + 4 * a * (1-a) * z * (1-z) + 4 * (1-a) ^ 2 * z ^ 2) +
    Real.sqrt (a ^ 2 + 4 * a * (1-a) * z * (1-z))) / 2

private def chi (a z : ℝ) : ℝ := Real.sqrt (a ^ 2 + 4 * a * (1-a) * z * (1-z))
private def nu (a z : ℝ) : ℝ :=
  Real.sqrt (a ^ 2 + 4 * a * (1-a) * z * (1-z) + 4 * (1-a) ^ 2 * z ^ 2)
private def denom (a z : ℝ) : ℝ := a + 2 * (1-a) * z + nu a z
private def negSize (a z : ℝ) : ℝ := nu a z * (nu a z-a) / denom a z

private def negVector (x y z : ℝ) : J → ℝ :=
  let t := 2 * x * y * z / denom (x ^ 2) z
  fun p => if p.1 = 0 then
    (if p.2 = 0 then -t * Real.sqrt (1-z) * x else 0)
    else (if p.2 = 0 then Real.sqrt z * (y * x-t) else -Real.sqrt z * y ^ 2)

private def noClickTest (x y z : ℝ) : Matrix J J ℂ :=
  fun i j => (negVector x y z i * negVector x y z j / negSize (x ^ 2) z : ℝ)

private def clickTest (a z : ℝ) : Matrix Q Q ℂ :=
  let h := (chi a z + a * (1-2 * z)) / (2 * chi a z)
  let t := Real.sqrt a * Real.sqrt (1-z) * Real.sqrt z / chi a z
  !![(h : ℂ), (t : ℂ); (t : ℂ), (1-h : ℝ)]

private def hN (x y z : ℝ) : ℝ :=
  (2 * x * y * z / denom (x ^ 2) z) ^ 2 * (1-z) * x ^ 2 / negSize (x ^ 2) z

private def hC (a z : ℝ) : ℝ :=
  (chi a z + a * (1-2 * z)) / (2 * chi a z)

private theorem scalar_bounds (a z : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hz : 1/2 ≤ z) (hz1 : z < 1) (hcond : 0 ≤ a + 2 * (1-2 * a) * z) :
    0 < chi a z ∧ a < nu a z ∧ 0 < denom a z ∧ 0 < negSize a z ∧
      1-z ≤ hC a z ∧ 0 ≤ hC a z ∧
      a * (a + 2 * (1-a) * z) ≤ (nu a z) ^ 2 := by
  have hb : 0 < 1-a := by linarith
  have hzp : 0 < z := by linarith
  have hzq : 0 < 1-z := by linarith
  have hrad : 0 < a ^ 2 + 4 * a * (1-a) * z * (1-z) := by positivity
  have hchi : 0 < chi a z := Real.sqrt_pos.mpr hrad
  have hcs : (chi a z) ^ 2 = a ^ 2 + 4 * a * (1-a) * z * (1-z) :=
    Real.sq_sqrt hrad.le
  have hns : (nu a z) ^ 2 = a ^ 2 + 4 * a * (1-a) * z * (1-z) + 4 * (1-a) ^ 2 * z ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hn : a < nu a z := by
    have hp : 0 ≤ nu a z := Real.sqrt_nonneg _
    have he : 0 < 4 * a * (1-a) * z * (1-z) := by positivity
    have he' : 0 ≤ 4 * (1-a) ^ 2 * z ^ 2 := by positivity
    nlinarith
  have hd : 0 < denom a z := by
    unfold denom
    nlinarith [mul_pos hb hzp]
  have hs : 0 < negSize a z := by unfold negSize; exact div_pos (mul_pos (by linarith) (by linarith)) hd
  have hca : a ≤ chi a z := by
    have he : 0 ≤ 4 * a * (1-a) * z * (1-z) := by positivity
    nlinarith
  have hh : 1-z ≤ hC a z := by
    unfold hC
    apply (le_div_iff₀ (by positivity : 0 < 2 * chi a z)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hca) (show 0 ≤ 2 * z-1 by linarith)]
  have hest : a * (a + 2 * (1-a) * z) ≤ (nu a z) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 2 * (1-a) * z by positivity) hcond]
  exact ⟨hchi, hn, hd, hs, hh, (by linarith), hest⟩

private theorem scalar_no_click (x y z : ℝ) (hxy : x ^ 2 + y ^ 2 = 1)
    (hx : 0 < x) (hy : 0 < y) (hz : 1/2 ≤ z) (hz1 : z < 1)
    (hcond : 0 ≤ x ^ 2 + 2 * (1-2 * x ^ 2) * z) : hN x y z ≤ hC (x ^ 2) z := by
  have ha : 0 < x ^ 2 := sq_pos_of_pos hx
  have ha1 : x ^ 2 < 1 := by nlinarith [sq_pos_of_pos hy]
  obtain ⟨hc, hn, hd, hs, hh, hcp, hest⟩ := scalar_bounds (x ^ 2) z ha ha1 hz hz1 hcond
  have hns : (nu (x ^ 2) z) ^ 2 =
      (x ^ 2) ^ 2 + 4 * x ^ 2 * (1-x ^ 2) * z * (1-z) + 4 * (1-x ^ 2) ^ 2 * z ^ 2 :=
    Real.sq_sqrt (by
      have hb : 0 ≤ 1-x ^ 2 := by linarith
      have hzp : 0 ≤ z := by linarith
      have hzq : 0 ≤ 1-z := by linarith
      positivity)
  have hT : (x ^ 2 + 2 * (1-x ^ 2) * z) ^ 2-(nu (x ^ 2) z) ^ 2 = 4 * x ^ 2 * y ^ 2 * z ^ 2 := by
    rw [hns]
    have hye : y ^ 2 = 1-x ^ 2 := by linarith
    rw [hye]
    ring
  have hle : hN x y z ≤ 1-z := by
    unfold hN negSize
    apply (div_le_iff₀ hs).mpr
    change (2 * x * y * z / denom (x ^ 2) z) ^ 2 * (1-z) * x ^ 2 ≤
      (1-z) * (nu (x ^ 2) z * (nu (x ^ 2) z-x ^ 2)/denom (x ^ 2) z)
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hd)).mp
    field_simp [hd.ne']
    have hid : denom (x ^ 2) z * (1-z) * nu (x ^ 2) z * (nu (x ^ 2) z-x ^ 2) -
        4 * x ^ 4 * y ^ 2 * z ^ 2 * (1-z) =
      denom (x ^ 2) z * (1-z) * ((nu (x ^ 2) z) ^ 2-x ^ 2 * (x ^ 2 + 2 * (1-x ^ 2) * z)) := by
      unfold denom
      linear_combination (x ^ 2 * (1-z)) * hT
    have he := mul_nonneg (mul_nonneg hd.le (show 0 ≤ 1-z by linarith))
      (sub_nonneg.mpr hest)
    nlinarith only [hid, he]
  exact hle.trans hh

private theorem neg_vector_norm (x y z : ℝ) (hxy : x ^ 2 + y ^ 2 = 1)
    (hx : 0 < x) (hy : 0 < y) (hz : 1/2 ≤ z) (hz1 : z < 1)
    (hcond : 0 ≤ x ^ 2 + 2 * (1-2 * x ^ 2) * z) :
    (∑ i : J, (negVector x y z i) ^ 2) = negSize (x ^ 2) z := by
  have ha : 0 < x ^ 2 := sq_pos_of_pos hx
  have ha1 : x ^ 2 < 1 := by nlinarith [sq_pos_of_pos hy]
  obtain ⟨hc, hn, hd, hs, hh, hcp, hest⟩ := scalar_bounds (x ^ 2) z ha ha1 hz hz1 hcond
  have hp : (Real.sqrt (1-z)) ^ 2 = 1-z := Real.sq_sqrt (by linarith)
  have hq : (Real.sqrt z) ^ 2 = z := Real.sq_sqrt (by linarith)
  have hv : (nu (x ^ 2) z) ^ 2 =
      (x ^ 2) ^ 2 + 4 * x ^ 2 * (1-x ^ 2) * z * (1-z) + 4 * (1-x ^ 2) ^ 2 * z ^ 2 :=
    Real.sq_sqrt (by
      have hb : 0 ≤ 1-x ^ 2 := by linarith
      have hzp : 0 ≤ z := by linarith
      have hzq : 0 ≤ 1-z := by linarith
      positivity)
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, negVector]
  norm_num
  simp only [mul_pow, div_pow, neg_sq, hp, hq]
  unfold negSize
  field_simp [hd.ne']
  unfold denom
  linear_combination (-(nu (x ^ 2) z) + (x ^ 2-1) * z) * hv +
    (z * (4 * x ^ 4 * z * (1-z) + x ^ 2 * (x ^ 2 + 2 * (1-x ^ 2) * z + nu (x ^ 2) z-2 * z) ^ 2 +
      (y ^ 2 + 1-x ^ 2) * (x ^ 2 + 2 * (1-x ^ 2) * z + nu (x ^ 2) z) ^ 2)) * hxy

private theorem test_projections (x y z : ℝ) (hxy : x ^ 2 + y ^ 2 = 1)
    (hx : 0 < x) (hy : 0 < y) (hz : 1/2 ≤ z) (hz1 : z < 1)
    (hcond : 0 ≤ x ^ 2 + 2 * (1-2 * x ^ 2) * z) :
    (noClickTest x y z)ᴴ = noClickTest x y z ∧
      noClickTest x y z * noClickTest x y z = noClickTest x y z ∧
      (clickTest (x ^ 2) z)ᴴ = clickTest (x ^ 2) z ∧
      clickTest (x ^ 2) z * clickTest (x ^ 2) z = clickTest (x ^ 2) z := by
  have ha : 0 < x ^ 2 := sq_pos_of_pos hx
  have ha1 : x ^ 2 < 1 := by nlinarith [sq_pos_of_pos hy]
  obtain ⟨hc, hn, hd, hs, hh, hcp, hest⟩ := scalar_bounds (x ^ 2) z ha ha1 hz hz1 hcond
  have hnorm := neg_vector_norm x y z hxy hx hy hz hz1 hcond
  have hp : (Real.sqrt (1-z)) ^ 2 = 1-z := Real.sq_sqrt (by linarith)
  have hq : (Real.sqrt z) ^ 2 = z := Real.sq_sqrt (by linarith)
  have hchi : (chi (x ^ 2) z) ^ 2 = (x ^ 2) ^ 2 + 4 * x ^ 2 * (1-x ^ 2) * z * (1-z) :=
    Real.sq_sqrt (by
      have hb : 0 ≤ 1-x ^ 2 := by linarith
      have hzp : 0 ≤ z := by linarith
      have hzq : 0 ≤ 1-z := by linarith
      positivity)
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    simp [noClickTest, Matrix.conjTranspose_apply, mul_comm]
  · ext i j
    simp only [Matrix.mul_apply, noClickTest, ← Complex.ofReal_mul,
      ← Complex.ofReal_sum]
    congr 1
    calc
      (∑ k : J, negVector x y z i * negVector x y z k / negSize (x ^ 2) z *
        (negVector x y z k * negVector x y z j / negSize (x ^ 2) z)) =
        negVector x y z i * negVector x y z j / (negSize (x ^ 2) z) ^ 2 *
          (∑ k : J, (negVector x y z k) ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ = negVector x y z i * negVector x y z j / negSize (x ^ 2) z := by
        rw [hnorm]
        field_simp [hs.ne']
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [clickTest, Matrix.conjTranspose_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [clickTest, Matrix.mul_apply, Fin.sum_univ_two, ← Complex.ofReal_mul,
        ← Complex.ofReal_add, ← Complex.ofReal_sub, Real.sqrt_sq hx.le] <;>
      norm_cast <;> field_simp [hc.ne'] <;>
      ring_nf <;> simp only [hp, hq] <;> nlinarith only [hchi]

private theorem orthogonal_sum_squares {k : Type*} [Fintype k]
    (c b : k → ℂ) (hc : ∑ j, Complex.normSq (c j) = 1)
    (hcb : ∑ j, star (c j) * b j = 0) (A B : ℝ) :
    (∑ j, Complex.normSq ((A : ℂ) * c j + (B : ℂ) * b j)) =
      A ^ 2 + B ^ 2 * (∑ j, Complex.normSq (b j)) := by
  have hr := congrArg Complex.re hcb
  simp only [Complex.re_sum, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im, Complex.zero_re] at hr
  calc
    (∑ j, Complex.normSq ((A : ℂ) * c j + (B : ℂ) * b j)) =
      (∑ j, (A ^ 2 * Complex.normSq (c j) + B ^ 2 * Complex.normSq (b j) +
        2 * A * B * ((c j).re * (b j).re + (c j).im * (b j).im))) := by
          apply Finset.sum_congr rfl
          intro j _
          simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
          ring
    _ = A ^ 2 + B ^ 2 * (∑ j, Complex.normSq (b j)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hc]
      have hr' : (∑ j, ((c j).re * (b j).re + (c j).im * (b j).im)) = 0 := by
        simpa only [neg_mul, sub_neg_eq_add] using hr
      rw [hr']
      ring

private def omega (x y z : ℝ) : J → ℂ :=
  fun p => if p.1 = 0 then
    (if p.2 = 0 then (Real.sqrt (1-z) * x : ℝ) else (-Real.sqrt (1-z) * y : ℝ))
    else (if p.2 = 0 then (Real.sqrt z : ℝ) else 0)

private theorem omega_unit (x y z : ℝ) (hxy : x ^ 2 + y ^ 2 = 1)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) : star (omega x y z) ⬝ᵥ omega x y z = 1 := by
  have hp := Real.sq_sqrt (show 0 ≤ 1-z by linarith)
  have hq := Real.sq_sqrt hz
  simp [omega, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
    ← Complex.ofReal_mul, ← Complex.ofReal_add]
  norm_cast
  nlinarith

private def liftedVector (K : Matrix O Q ℂ) (v : J → ℂ) : JO → ℂ :=
  fun p => ∑ i : Q, K p.2 i * v (p.1, i)

private theorem reference_kraus {k : Type*} [Fintype k]
    (F : QuantumChannel Q O) (K : k → Matrix O Q ℂ)
    (hK : ∀ X : Matrix Q Q ℂ,
      CStarMatrix.ofMatrix.symm (F.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        ∑ j, K j * X * (K j)ᴴ)
    (v : J → ℂ) : CStarMatrix.ofMatrix.symm
      (referenceLinear F (CStarMatrix.ofMatrix (outer v))) =
        ∑ j, outer (liftedVector (K j) v) := by
  ext p q
  have he := congrArg (fun M : Matrix O O ℂ => M p.2 q.2)
    (hK (Matrix.of fun i l => outer v (p.1, i) (q.1, l)))
  change F.toCompletelyPositiveMap
    (CStarMatrix.ofMatrix fun i l => outer v (p.1, i) (q.1, l)) p.2 q.2 = _ at he
  change F.toCompletelyPositiveMap
    (CStarMatrix.ofMatrix fun i l => outer v (p.1, i) (q.1, l)) p.2 q.2 = _
  rw [he]
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    outer, Matrix.vecMulVec_apply, Pi.star_apply, liftedVector,
    star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  dsimp only [Matrix.of_apply]
  ring

private def jointTest (x y z : ℝ) : Matrix JO JO ℂ :=
  fun p q => if p.2.1 = q.2.1 then
    (if p.2.1 then (clickTest (x ^ 2) z ⊗ₖ (1 : Matrix Q Q ℂ))
      (p.1, p.2.2) (q.1, q.2.2)
     else noClickTest x y z (p.1, p.2.2) (q.1, q.2.2)) else 0

private theorem joint_test_projection (x y z : ℝ) (hxy : x ^ 2 + y ^ 2 = 1)
    (hx : 0 < x) (hy : 0 < y) (hz : 1/2 ≤ z) (hz1 : z < 1)
    (hcond : 0 ≤ x ^ 2 + 2 * (1-2 * x ^ 2) * z) :
    (jointTest x y z)ᴴ = jointTest x y z ∧
      jointTest x y z * jointTest x y z = jointTest x y z := by
  obtain ⟨hN, hNN, hC, hCC⟩ := test_projections x y z hxy hx hy hz hz1 hcond
  constructor
  · ext ⟨i, s, u⟩ ⟨j, t, v⟩
    have hne := congrArg (fun M : Matrix J J ℂ => M (i, u) (j, v)) hN
    have hce := congrArg (fun M : Matrix Q Q ℂ => M i j) hC
    cases s <;> cases t <;> fin_cases u <;> fin_cases v <;>
      simp_all [jointTest, Matrix.conjTranspose_apply, Matrix.one_apply,
        Matrix.kroneckerMap_apply]
  · ext ⟨i, s, u⟩ ⟨j, t, v⟩
    have hne := congrArg (fun M : Matrix J J ℂ => M (i, u) (j, v)) hNN
    have hce := congrArg (fun M : Matrix Q Q ℂ => M i j) hCC
    cases s <;> cases t <;> fin_cases u <;> fin_cases v <;>
      simp_all [jointTest, Matrix.mul_apply, Fintype.sum_prod_type,
        Fin.sum_univ_two, Matrix.one_apply, Matrix.kroneckerMap_apply]

private def amplitudeU (x y z : ℝ) : ℝ :=
  negVector x y z (0, 0) * Real.sqrt (1-z) * x + negVector x y z (1, 0) * Real.sqrt z

private def amplitudeQ (x y z : ℝ) : ℝ :=
  Real.sqrt z * y * (negVector x y z (1, 0) * x-negVector x y z (1, 1) * y)

private theorem baseline_mass (x y z : ℝ) (hxy : x ^ 2 + y ^ 2 = 1)
    (hx : 0 < x) (hy : 0 < y) (hz : 1/2 ≤ z) (hz1 : z < 1)
    (hcond : 0 ≤ x ^ 2 + 2 * (1-2 * x ^ 2) * z) :
    (amplitudeQ x y z) ^ 2 / negSize (x ^ 2) z +
      (hC (x ^ 2) z * (1-z) + 2 * x * Real.sqrt (1-z) * Real.sqrt z *
        (Real.sqrt (x ^ 2) * Real.sqrt (1-z) * Real.sqrt z / chi (x ^ 2) z) +
        (1-hC (x ^ 2) z) * x ^ 2 * z) -
      ((amplitudeU x y z) ^ 2 / negSize (x ^ 2) z + (1-z) * y ^ 2 * hC (x ^ 2) z) =
      (nu (x ^ 2) z + chi (x ^ 2) z)/2 := by
  have ha : 0 < x ^ 2 := sq_pos_of_pos hx
  have ha1 : x ^ 2 < 1 := by nlinarith [sq_pos_of_pos hy]
  obtain ⟨hc, hn, hd, hs, hh, hcp, hest⟩ := scalar_bounds (x ^ 2) z ha ha1 hz hz1 hcond
  have hp : (Real.sqrt (1-z)) ^ 2 = 1-z := Real.sq_sqrt (by linarith)
  have hq : (Real.sqrt z) ^ 2 = z := Real.sq_sqrt (by linarith)
  have hchi : (chi (x ^ 2) z) ^ 2 = (x ^ 2) ^ 2 + 4 * x ^ 2 * (1-x ^ 2) * z * (1-z) :=
    Real.sq_sqrt (by
      have hb : 0 ≤ 1-x ^ 2 := by linarith
      have hzp : 0 ≤ z := by linarith
      have hzq : 0 ≤ 1-z := by linarith
      positivity)
  have hv : (nu (x ^ 2) z) ^ 2 =
      (x ^ 2) ^ 2 + 4 * x ^ 2 * (1-x ^ 2) * z * (1-z) + 4 * (1-x ^ 2) ^ 2 * z ^ 2 :=
    Real.sq_sqrt (by
      have hb : 0 ≤ 1-x ^ 2 := by linarith
      have hzp : 0 ≤ z := by linarith
      have hzq : 0 ≤ 1-z := by linarith
      positivity)
  have hno : (amplitudeQ x y z) ^ 2-(amplitudeU x y z) ^ 2 =
      negSize (x ^ 2) z * (nu (x ^ 2) z-x ^ 2)/2 := by
    have hu : amplitudeU x y z = x * y * z * (nu (x ^ 2) z-x ^ 2)/denom (x ^ 2) z := by
      unfold amplitudeU
      simp [negVector]
      ring_nf
      simp only [hp, hq]
      field_simp [hd.ne']
      unfold denom
      ring
    have hq' : amplitudeQ x y z =
        y ^ 2 * z * (denom (x ^ 2) z-2 * x ^ 2 * z)/denom (x ^ 2) z := by
      unfold amplitudeQ
      simp [negVector]
      ring_nf
      simp only [hq]
      field_simp [hd.ne']
      linear_combination (denom (x ^ 2) z) * hxy
    rw [hu, hq']
    unfold negSize
    field_simp [hd.ne']
    unfold denom
    linear_combination
      (-(nu (x ^ 2) z) ^ 2 + (2 * x ^ 2 * z + x ^ 2-2 * z) * nu (x ^ 2) z -
        4 * x ^ 4 * z ^ 2 + 6 * x ^ 2 * z ^ 2-2 * z ^ 2) * hv +
      (2 * z ^ 2 * ((y ^ 2 + 1-x ^ 2) * (x ^ 2 + 2 * (1-x ^ 2) * z + nu (x ^ 2) z-2 * x ^ 2 * z) ^ 2 -
        x ^ 2 * (nu (x ^ 2) z-x ^ 2) ^ 2)) * hxy
  have hclick : hC (x ^ 2) z * (1-z) + 2 * x * Real.sqrt (1-z) * Real.sqrt z *
      (Real.sqrt (x ^ 2) * Real.sqrt (1-z) * Real.sqrt z / chi (x ^ 2) z) +
      (1-hC (x ^ 2) z) * x ^ 2 * z - (1-z) * y ^ 2 * hC (x ^ 2) z =
      (x ^ 2 + chi (x ^ 2) z)/2 := by
    rw [Real.sqrt_sq hx.le]
    unfold hC
    field_simp [hc.ne']
    ring_nf
    simp only [hp, hq]
    linear_combination -hchi - (x ^ 2 * (1-2 * z) + chi (x ^ 2) z) * (1-z) * hxy
  have hno' : (amplitudeQ x y z) ^ 2 / negSize (x ^ 2) z -
      (amplitudeU x y z) ^ 2 / negSize (x ^ 2) z = (nu (x ^ 2) z-x ^ 2)/2 := by
    rw [← sub_div, hno]
    field_simp [hs.ne']
  linarith

private theorem actual_test_value {k : Type*} [Fintype k]
    (K : k → Matrix O Q ℂ) (x y z : ℝ)
    (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hcol : ∀ j p, K j p 0 = if p = (false, 0) then K j (false, 0) 0 else 0)
    (hc : ∑ j, Complex.normSq (K j (false, 0) 0) = 1)
    (hcb : ∑ j, star (K j (false, 0) 0) * K j (false, 0) 1 = 0) :
    (Matrix.trace (jointTest x y z *
      (∑ j, outer (liftedVector (K j) (omega x y z))))).re =
    (amplitudeU x y z) ^ 2 / negSize (x ^ 2) z +
      (1-z) * y ^ 2 * hN x y z * (∑ j, Complex.normSq (K j (false, 0) 1)) +
      (1-z) * y ^ 2 * hC (x ^ 2) z * (∑ j, ∑ i : Q, Complex.normSq (K j (true, i) 1)) := by
  have hvalue (M : Matrix O Q ℂ)
      (hM : ∀ p, M p 0 = if p = (false, 0) then M (false, 0) 0 else 0) :
      (Matrix.trace (jointTest x y z * outer (liftedVector M (omega x y z)))).re =
      Complex.normSq ((amplitudeU x y z : ℂ) * M (false, 0) 0-
        (Real.sqrt (1-z) * y * negVector x y z (0, 0) : ℝ) * M (false, 0) 1) /
          negSize (x ^ 2) z +
      (Real.sqrt (1-z)) ^ 2 * y ^ 2 * hC (x ^ 2) z *
        (∑ i : Q, Complex.normSq (M (true, i) 1)) := by
    have h01 := hM (false, 1)
    have h10 := hM (true, 0)
    have h11 := hM (true, 1)
    simp only [show (false, (1 : Q)) ≠ (false, 0) by decide,
      show (true, (0 : Q)) ≠ (false, 0) by decide,
      show (true, (1 : Q)) ≠ (false, 0) by decide, if_false] at h01 h10 h11
    simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, outer,
      Matrix.vecMulVec_apply, jointTest, noClickTest, clickTest,
      liftedVector, omega, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.one_apply, Matrix.kroneckerMap_apply, h01, h10, h11,
      negVector, amplitudeU, hC, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im, ← Complex.ofReal_div]
    ring
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  simp_rw [hvalue _ (hcol _)]
  rw [Finset.sum_add_distrib, ← Finset.sum_div]
  have hsum := orthogonal_sum_squares (fun j => K j (false, 0) 0)
    (fun j => K j (false, 0) 1) hc hcb (amplitudeU x y z)
      (-Real.sqrt (1-z) * y * negVector x y z (0, 0))
  simp only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg] at hsum
  rw [hsum]
  have hp := Real.sq_sqrt (show 0 ≤ 1-z by linarith)
  rw [← Finset.mul_sum]
  simp only [hN, negVector, if_true]
  ring_nf
  simp only [show (Real.sqrt (1-z)) ^ 4 = ((Real.sqrt (1-z)) ^ 2) ^ 2 by ring, hp]
  try simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

private def nominalMatrix (x y : ℝ) (X : Matrix Q Q ℂ) : Matrix O O ℂ :=
  fun p q => if p.1 = q.1 then
    (if p.1 then
      (x : ℂ) ^ 2 * X 0 0-(x : ℂ) * (y : ℂ) * (X 0 1 + X 1 0) + (y : ℂ) ^ 2 * X 1 1
    else (y : ℂ) ^ 2 * X 0 0 + (x : ℂ) * (y : ℂ) * (X 0 1 + X 1 0) + (x : ℂ) ^ 2 * X 1 1) *
      (if p.2 = 0 then (x : ℂ) else -y) * (if q.2 = 0 then (x : ℂ) else -y)
    else 0

private theorem nominal_test_value (G : QuantumChannel Q O) (x y z : ℝ)
    (hxy : x ^ 2 + y ^ 2 = 1) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hG : ∀ X : Matrix Q Q ℂ,
      CStarMatrix.ofMatrix.symm (G.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        nominalMatrix x y X) :
    (Matrix.trace (jointTest x y z * CStarMatrix.ofMatrix.symm
      (referenceLinear G (CStarMatrix.ofMatrix (outer (omega x y z)))))).re =
      (amplitudeQ x y z) ^ 2/negSize (x ^ 2) z +
        hC (x ^ 2) z * (1-z) + 2 * x * Real.sqrt (1-z) * Real.sqrt z *
          (Real.sqrt (x ^ 2) * Real.sqrt (1-z) * Real.sqrt z / chi (x ^ 2) z) +
          (1-hC (x ^ 2) z) * x ^ 2 * z := by
  have he (p q : JO) : referenceLinear G
      (CStarMatrix.ofMatrix (outer (omega x y z))) p q =
      nominalMatrix x y (fun i j => outer (omega x y z) (p.1, i) (q.1, j)) p.2 q.2 := by
    exact congrArg (fun M : Matrix O O ℂ => M p.2 q.2)
      (hG (fun i j => outer (omega x y z) (p.1, i) (q.1, j)))
  have hw : CStarMatrix.ofMatrix.symm
      (referenceLinear G (CStarMatrix.ofMatrix (outer (omega x y z)))) =
      fun p q => nominalMatrix x y
        (fun i j => outer (omega x y z) (p.1, i) (q.1, j)) p.2 q.2 := by
    ext p q
    exact he p q
  rw [hw]
  have hs : (Real.sqrt z) ^ 2 = z := Real.sq_sqrt hz
  have hs' : (Real.sqrt (1-z)) ^ 2 = 1-z := Real.sq_sqrt (by linarith)
  change (∑ i : JO, ∑ j : JO, jointTest x y z i j *
    nominalMatrix x y (fun u v => outer (omega x y z) (j.1, u) (i.1, v)) j.2 i.2).re = _
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two,
    nominalMatrix, omega, outer, Matrix.vecMulVec_apply, jointTest,
    noClickTest, clickTest, negVector, amplitudeQ, hC,
    Matrix.one_apply, Matrix.kroneckerMap_apply, ← Complex.ofReal_pow,
    Complex.mul_re, Complex.mul_im]
  have hy2 : y ^ 2 = 1-x ^ 2 := by linarith
  try ring_nf
  try simp only [show y ^ 4 = (y ^ 2) ^ 2 by ring, show y ^ 6 = (y ^ 2) ^ 3 by ring,
    show y ^ 8 = (y ^ 2) ^ 4 by ring, hy2]
  try ring_nf
  try simp only [show y ^ 4 = (y ^ 2) ^ 2 by ring, show y ^ 6 = (y ^ 2) ^ 3 by ring, hy2]
  simp only [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_add,
    ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re]
  norm_num [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]
  try simp only [hs, hs']
  ring

private theorem actual_reference_lower_bound_basis (F G : QuantumChannel Q O)
    (x y z : ℝ) (hxy : x ^ 2 + y ^ 2 = 1) (hx : 0 < x) (hy : 0 < y)
    (hz : 1/2 ≤ z) (hz1 : z < 1) (hcond : 0 ≤ x ^ 2 + 2 * (1-2 * x ^ 2) * z)
    (hfixed : F.toCompletelyPositiveMap
      (CStarMatrix.ofMatrix (Matrix.single (0 : Q) (0 : Q) (1 : ℂ))) =
        CStarMatrix.ofMatrix (Matrix.single (false, 0) (false, 0) (1 : ℂ)))
    (hG : ∀ X : Matrix Q Q ℂ,
      CStarMatrix.ofMatrix.symm (G.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        nominalMatrix x y X) : referenceLowerBound (x ^ 2) z ≤ diamondDistance F G/2 := by
  obtain ⟨K, hcomp, hK⟩ := channel_kraus_stinespring.1 F
  have hfix : (∑ j, K j * Matrix.single (0 : Q) (0 : Q) (1 : ℂ) * (K j)ᴴ) =
      Matrix.single (false, 0) (false, 0) (1 : ℂ) := by
    rw [← hK]
    exact congrArg CStarMatrix.ofMatrix.symm hfixed
  obtain ⟨hcol, hc, hcb⟩ := kraus_pure_column K hfix hcomp
  let rho : DensityState J := pureState (omega x y z)
    (omega_unit x y z hxy (by linarith) hz1.le)
  have htF := actual_test_value K x y z (by linarith) hz1.le hcol hc hcb
  have htG := nominal_test_value G x y z hxy (by linarith) hz1.le hG
  have hm := baseline_mass x y z hxy hx hy hz hz1 hcond
  have hcoeff := scalar_no_click x y z hxy hx hy hz hz1 hcond
  have hcpos := (scalar_bounds (x ^ 2) z (sq_pos_of_pos hx)
    (by nlinarith [sq_pos_of_pos hy]) hz hz1 hcond).2.2.2.2.2.1
  have hcomplete : (∑ j, ∑ p : O, Complex.normSq (K j p 1)) = 1 := by
    have h := congrArg (fun M : Matrix Q Q ℂ => (M 1 1).re) hcomp
    simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.normSq_apply, Complex.mul_re] using h
  have hparts : (∑ j, Complex.normSq (K j (false, 0) 1)) +
      (∑ j, Complex.normSq (K j (false, 1) 1)) +
      (∑ j, ∑ i : Q, Complex.normSq (K j (true, i) 1)) = 1 := by
    have h : (∑ j, ∑ p : O, Complex.normSq (K j p 1)) =
        (∑ j, Complex.normSq (K j (false, 0) 1)) +
        (∑ j, Complex.normSq (K j (false, 1) 1)) +
        (∑ j, ∑ i : Q, Complex.normSq (K j (true, i) 1)) := by
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_two,
        Finset.sum_add_distrib]
      ring
    linarith only [h, hcomplete]
  have hval : referenceLowerBound (x ^ 2) z ≤
      -(Matrix.trace (jointTest x y z *
        (CStarMatrix.ofMatrix.symm (referenceState F rho).1 -
          CStarMatrix.ofMatrix.symm (referenceState G rho).1))).re := by
    change referenceLowerBound (x ^ 2) z ≤
      -(Matrix.trace (jointTest x y z *
        (CStarMatrix.ofMatrix.symm (referenceLinear F
            (CStarMatrix.ofMatrix (outer (omega x y z)))) -
          CStarMatrix.ofMatrix.symm (referenceLinear G
            (CStarMatrix.ofMatrix (outer (omega x y z))))))).re
    rw [reference_kraus F K hK]
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, htF, htG]
    change (nu (x ^ 2) z + chi (x ^ 2) z)/2 ≤ _
    have hp : 0 ≤ (1-z) * y ^ 2 := by positivity
    have hb : 0 ≤ ∑ j, Complex.normSq (K j (false, 0) 1) :=
      Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _)
    have hv : 0 ≤ ∑ j, Complex.normSq (K j (false, 1) 1) :=
      Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _)
    have hparts' := congrArg (fun t : ℝ => (1-z) * y ^ 2 * hC (x ^ 2) z * t) hparts
    nlinarith only [hm, hparts',
      mul_nonneg (mul_nonneg hp (sub_nonneg.mpr hcoeff)) hb,
      mul_nonneg (mul_nonneg hp hcpos) hv]
  have hprojection := joint_test_projection x y z hxy hx hy hz hz1 hcond
  have htr : Matrix.trace (CStarMatrix.ofMatrix.symm (referenceState F rho).1 -
      CStarMatrix.ofMatrix.symm (referenceState G rho).1) = 0 := by
    rw [Matrix.trace_sub]
    change Matrix.trace (referenceState F rho).1-Matrix.trace (referenceState G rho).1 = 0
    rw [DensityState.trace_eq_one, DensityState.trace_eq_one, sub_self]
  have htest := projection_test_bound _ _ hprojection.1 hprojection.2 htr
  have hbdd : BddAbove ({0} ∪ {t : ℝ | ∃ n : ℕ, ∃ sigma : DensityState (Fin n × Q),
      t = referenceError F G sigma}) := by
    refine ⟨2, ?_⟩
    rintro t (ht | ⟨n, sigma, rfl⟩)
    · simpa only [Set.mem_singleton_iff] using ht.le.trans (by norm_num)
    · have h := traceDistance_le_one (referenceState F sigma) (referenceState G sigma)
      change referenceError F G sigma/2 ≤ 1 at h
      linarith
  have hd : referenceError F G rho ≤ diamondDistance F G :=
    le_csSup hbdd (Or.inr ⟨2, rho, rfl⟩)
  exact hval.trans (htest.trans (div_le_div_of_nonneg_right hd (by norm_num)))

private def unitaryChannel {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hU : Uᴴ * U = 1) : QuantumChannel n n :=
  Classical.choose (finite_kraus_quantum_channel (fun _ : Unit => U) (by simpa using hU))

private theorem unitary_channel_apply {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hU : Uᴴ * U = 1) (X : CStarMatrix n n ℂ) :
    (unitaryChannel U hU).toCompletelyPositiveMap X =
      CStarMatrix.ofMatrix (U * CStarMatrix.ofMatrix.symm X * Uᴴ) := by
  have h := Classical.choose_spec
    (finite_kraus_quantum_channel (fun _ : Unit => U) (by simpa using hU))
  simpa [unitaryChannel] using congrArg CStarMatrix.ofMatrix (h (CStarMatrix.ofMatrix.symm X))

private theorem unitary_reference_apply {r n : Type*} [Fintype r] [DecidableEq r]
    [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hU : Uᴴ * U = 1)
    (X : CStarMatrix (r × n) (r × n) ℂ) :
    referenceLinear (unitaryChannel U hU) X = CStarMatrix.ofMatrix
      (((1 : Matrix r r ℂ) ⊗ₖ U) * CStarMatrix.ofMatrix.symm X * ((1 : Matrix r r ℂ) ⊗ₖ U)ᴴ) := by
  ext ⟨i, u⟩ ⟨j, v⟩
  change (unitaryChannel U hU).toCompletelyPositiveMap
    (CStarMatrix.ofMatrix fun x y => X (i, x) (j, y)) u v = _
  rw [unitary_channel_apply]
  change (U * (Matrix.of fun x y => X (i, x) (j, y)) * Uᴴ) u v =
    (((1 : Matrix r r ℂ) ⊗ₖ U) * (Matrix.of fun p q => X p q) *
      ((1 : Matrix r r ℂ) ⊗ₖ U)ᴴ) (i, u) (j, v)
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, mul_ite, ite_mul, apply_ite]

private theorem reference_comp {r a b c : Type*}
    [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (F : QuantumChannel a b) (G : QuantumChannel b c)
    (X : CStarMatrix (r × a) (r × a) ℂ) :
    referenceLinear (G.comp F) X = referenceLinear G (referenceLinear F X) := by
  ext ⟨i, u⟩ ⟨j, v⟩
  rfl

private theorem unitary_error_postprocess {r : Type*} [Fintype r] [DecidableEq r]
    (F G : QuantumChannel Q O)
    (U : Matrix O O ℂ) (hU : Uᴴ * U = 1) (rho : DensityState (r × Q)) :
    referenceError ((unitaryChannel U hU).comp F)
      ((unitaryChannel U hU).comp G) rho ≤ referenceError F G rho := by
  let V := (1 : Matrix r r ℂ) ⊗ₖ U
  have hV : Vᴴ * V = 1 := by
    simp only [V, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, hU, Matrix.one_kronecker_one]
  have he (C : QuantumChannel Q O) :
      referenceState ((unitaryChannel U hU).comp C) rho =
        (unitaryChannel V hV).mapState (referenceState C rho) := by
    apply Subtype.ext
    change referenceLinear ((unitaryChannel U hU).comp C) rho.1 = _
    rw [reference_comp, unitary_reference_apply]
    exact (unitary_channel_apply V hV (referenceState C rho).1).symm
  have ht := traceDistance_contract (unitaryChannel V hV)
    (referenceState F rho) (referenceState G rho)
  rw [← he F, ← he G] at ht
  change referenceError ((unitaryChannel U hU).comp F)
    ((unitaryChannel U hU).comp G) rho/2 ≤ referenceError F G rho/2 at ht
  linarith

private def basisMatrix (x y : ℝ) (t : ℂ) : Matrix Q Q ℂ :=
  !![(x : ℂ), (-y : ℝ); (y : ℂ) * t, (x : ℂ) * t]

private theorem basis_unitary (x y : ℝ) (t : ℂ) (hxy : x ^ 2 + y ^ 2 = 1)
    (ht : star t * t = 1) : (basisMatrix x y t)ᴴ * basisMatrix x y t = 1 ∧
      basisMatrix x y t * (basisMatrix x y t)ᴴ = 1 := by
  have hxyC : (x : ℂ) ^ 2 + (y : ℂ) ^ 2 = 1 := by exact_mod_cast hxy
  have htt : t * star t = 1 := by rw [mul_comm]; exact ht
  have ht' : (starRingEnd ℂ) t * t = 1 := ht
  have htt' : t * (starRingEnd ℂ) t = 1 := htt
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [basisMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Matrix.one_apply, star_mul] <;>
    try ring_nf
  all_goals try simp only [mul_assoc, ht', htt']
  all_goals
    first
    | solve | ring
    | linear_combination hxyC

private def recordBasis (U : Matrix Q Q ℂ) : Matrix O O ℂ :=
  (1 : Matrix Bool Bool ℂ) ⊗ₖ U

private theorem record_basis_gram (U : Matrix Q Q ℂ) (hU : Uᴴ * U = 1) :
    (recordBasis U)ᴴ * recordBasis U = 1 := by
  simp [recordBasis, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU]

/-- The original instrument retains the two orthogonal records and both successors. -/
def nominalInstrument : QuantumChannel Q O :=
  Classical.choose (finite_kraus_quantum_channel
    (fun k : Bool => if k then Matrix.single (true, (0 : Q)) (0 : Q) (1 : ℂ)
      else Matrix.single (false, (0 : Q)) (1 : Q) (1 : ℂ))
    (by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Fintype.sum_bool, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.single, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply]))

private theorem nominal_instrument_apply (X : Matrix Q Q ℂ) :
    CStarMatrix.ofMatrix.symm (nominalInstrument.toCompletelyPositiveMap
      (CStarMatrix.ofMatrix X)) =
      fun p q => if p = (false, 0) ∧ q = (false, 0) then X 1 1
        else if p = (true, 0) ∧ q = (true, 0) then X 0 0 else 0 := by
  have h := Classical.choose_spec (finite_kraus_quantum_channel
    (fun k : Bool => if k then Matrix.single (true, (0 : Q)) (0 : Q) (1 : ℂ)
      else Matrix.single (false, (0 : Q)) (1 : Q) (1 : ℂ))
    (by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Fintype.sum_bool, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.single, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply]))
  change CStarMatrix.ofMatrix.symm (nominalInstrument.toCompletelyPositiveMap
    (CStarMatrix.ofMatrix X)) = _
  rw [show CStarMatrix.ofMatrix.symm (nominalInstrument.toCompletelyPositiveMap
    (CStarMatrix.ofMatrix X)) = _ from h X]
  ext ⟨s, i⟩ ⟨r, j⟩
  cases s <;> cases r <;> fin_cases i <;> fin_cases j <;>
    simp [Fintype.sum_bool, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.single, Fin.sum_univ_two]

private theorem diamond_two_sided (F G : QuantumChannel Q O)
    (V : Matrix Q Q ℂ) (hV : Vᴴ * V = 1)
    (U : Matrix O O ℂ) (hU : Uᴴ * U = 1) :
    diamondDistance ((unitaryChannel U hU).comp (F.comp (unitaryChannel V hV)))
      ((unitaryChannel U hU).comp (G.comp (unitaryChannel V hV))) ≤ diamondDistance F G := by
  have hbdd : BddAbove ({0} ∪ {t : ℝ | ∃ n : ℕ, ∃ sigma : DensityState (Fin n × Q),
      t = referenceError F G sigma}) := by
    refine ⟨2, ?_⟩
    rintro t (ht | ⟨n, sigma, rfl⟩)
    · have h : t = 0 := Set.mem_singleton_iff.mp ht
      subst t
      norm_num
    · have h := traceDistance_le_one (referenceState F sigma) (referenceState G sigma)
      change referenceError F G sigma/2 ≤ 1 at h
      linarith
  have h0 : 0 ≤ diamondDistance F G := le_csSup hbdd (Or.inl (Set.mem_singleton 0))
  apply csSup_le
  · exact ⟨0, Or.inl (Set.mem_singleton 0)⟩
  · rintro e (he | ⟨n, rho, rfl⟩)
    · have h : e = 0 := Set.mem_singleton_iff.mp he
      subst e
      exact h0
    · have hp := unitary_error_postprocess (F.comp (unitaryChannel V hV))
        (G.comp (unitaryChannel V hV)) U hU rho
      have hpre : referenceError (F.comp (unitaryChannel V hV))
          (G.comp (unitaryChannel V hV)) rho =
          referenceError F G (referenceState (unitaryChannel V hV) rho) := by
        unfold referenceError
        change traceNorm
          (CStarMatrix.ofMatrix.symm (referenceLinear (F.comp (unitaryChannel V hV)) rho.1)-
            CStarMatrix.ofMatrix.symm (referenceLinear (G.comp (unitaryChannel V hV)) rho.1)) = _
        rw [reference_comp, reference_comp]
        rfl
      rw [hpre] at hp
      exact hp.trans (le_csSup hbdd
        (Or.inr ⟨n, referenceState (unitaryChannel V hV) rho, rfl⟩))

private theorem basis_nominal (x y : ℝ) (t : ℂ) (hxy : x ^ 2 + y ^ 2 = 1)
    (ht : star t * t = 1) (X : Matrix Q Q ℂ) :
    let U := basisMatrix x y t
    let h := basis_unitary x y t hxy ht
    let V := recordBasis Uᴴ
    CStarMatrix.ofMatrix.symm
      (((unitaryChannel V (record_basis_gram Uᴴ
          (by simpa using h.2))).comp
        (nominalInstrument.comp (unitaryChannel U h.1))).toCompletelyPositiveMap
          (CStarMatrix.ofMatrix X)) = nominalMatrix x y X := by
  dsimp only
  rw [QuantumChannel.comp_apply, QuantumChannel.comp_apply]
  rw [unitary_channel_apply (basisMatrix x y t)]
  rw [unitary_channel_apply]
  simp only [Equiv.symm_apply_apply]
  rw [nominal_instrument_apply]
  change recordBasis (basisMatrix x y t)ᴴ *
    (Matrix.of fun p q : O =>
      if p = (false, 0) ∧ q = (false, 0) then
        (basisMatrix x y t * X * (basisMatrix x y t)ᴴ) 1 1
      else if p = (true, 0) ∧ q = (true, 0) then
        (basisMatrix x y t * X * (basisMatrix x y t)ᴴ) 0 0 else 0) *
    (recordBasis (basisMatrix x y t)ᴴ)ᴴ = nominalMatrix x y X
  ext ⟨s, i⟩ ⟨r, j⟩
  simp only [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  have hxyC : (x : ℂ) ^ 2 + (y : ℂ) ^ 2 = 1 := by exact_mod_cast hxy
  have htt : t * star t = 1 := by rw [mul_comm]; exact ht
  have htt' : t * (starRingEnd ℂ) t = 1 := htt
  have ht' : (starRingEnd ℂ) t * t = 1 := ht
  cases s <;> cases r <;> fin_cases i <;> fin_cases j <;>
    simp [nominalMatrix, recordBasis, basisMatrix, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Matrix.one_apply, star_mul] <;>
    try ring_nf
  all_goals try simp only [true_or]
  all_goals try apply Or.inl
  all_goals simp only [mul_assoc, mul_left_comm t, htt', ht', one_mul, mul_one]
  all_goals ring

/-- A pure dark state with arbitrary relative phase. -/
private def darkState (x y : ℝ) (t : ℂ) : CStarMatrix Q Q ℂ :=
  CStarMatrix.ofMatrix (basisMatrix x y t * Matrix.single (0 : Q) 0 (1 : ℂ) *
    (basisMatrix x y t)ᴴ)

/-- The same dark state in the no-click record of the original interface. -/
private def darkRecordState (x y : ℝ) (t : ℂ) : CStarMatrix O O ℂ :=
  CStarMatrix.ofMatrix (recordBasis (basisMatrix x y t) *
    Matrix.single (false, 0) (false, 0) (1 : ℂ) * (recordBasis (basisMatrix x y t))ᴴ)

/-- Every actual legal channel with a pure no-click fixed state satisfies the
uniform reference-test estimate, including arbitrary quantum clicked successors. -/
private theorem reference_lower_bound_phase (F : QuantumChannel (Fin 2) (Bool × Fin 2))
    (x y z : ℝ) (t : ℂ) (hxy : x ^ 2 + y ^ 2 = 1) (hx : 0 < x) (hy : 0 < y)
    (ht : star t * t = 1) (hz : 1/2 ≤ z) (hz1 : z < 1)
    (hcond : 0 ≤ x ^ 2 + 2 * (1-2 * x ^ 2) * z)
    (hfixed : F.toCompletelyPositiveMap (darkState x y t) = darkRecordState x y t) :
    referenceLowerBound (x ^ 2) z ≤ diamondDistance F nominalInstrument/2 := by
  let U := basisMatrix x y t
  have hu := basis_unitary x y t hxy ht
  let pre := unitaryChannel U hu.1
  let V := recordBasis Uᴴ
  have hv : Vᴴ * V = 1 := record_basis_gram Uᴴ (by simpa using hu.2)
  let post := unitaryChannel V hv
  have hvu : recordBasis Uᴴ * recordBasis U = 1 := by
    change recordBasis Uᴴ * recordBasis U = 1
    have hu' : Uᴴ * U = 1 := hu.1
    simp [recordBasis, ← Matrix.mul_kronecker_mul, hu']
  have hfix : (post.comp (F.comp pre)).toCompletelyPositiveMap
      (CStarMatrix.ofMatrix (Matrix.single (0 : Q) 0 (1 : ℂ))) =
      CStarMatrix.ofMatrix (Matrix.single (false, 0) (false, 0) (1 : ℂ)) := by
    rw [QuantumChannel.comp_apply, QuantumChannel.comp_apply]
    rw [show pre.toCompletelyPositiveMap
      (CStarMatrix.ofMatrix (Matrix.single (0 : Q) 0 (1 : ℂ))) = darkState x y t from
        unitary_channel_apply U hu.1 _]
    rw [hfixed, unitary_channel_apply]
    apply congrArg CStarMatrix.ofMatrix
    change V * (recordBasis U * Matrix.single (false, 0) (false, 0) (1 : ℂ) *
      (recordBasis U)ᴴ) * Vᴴ = _
    have hvu' : V * recordBasis U = 1 := hvu
    calc
      _ = (V * recordBasis U) * Matrix.single (false, 0) (false, 0) (1 : ℂ) *
          (V * recordBasis U)ᴴ := by simp [Matrix.mul_assoc, Matrix.conjTranspose_mul]
      _ = _ := by rw [hvu']; simp
  have hbound := actual_reference_lower_bound_basis (post.comp (F.comp pre))
    (post.comp (nominalInstrument.comp pre)) x y z hxy hx hy hz hz1 hcond hfix
      (basis_nominal x y t hxy ht)
  have hd := diamond_two_sided F nominalInstrument U hu.1 V hv
  exact hbound.trans (div_le_div_of_nonneg_right hd (by norm_num))

private theorem phase_representation (psi : Q → ℂ)
    (hu : Complex.normSq (psi 0) + Complex.normSq (psi 1) = 1)
    (ha : 0 < Complex.normSq (psi 0)) (ha1 : Complex.normSq (psi 0) < 1) :
    ∃ x y : ℝ, ∃ t : ℂ, x ^ 2 + y ^ 2 = 1 ∧ 0 < x ∧ 0 < y ∧ star t * t = 1 ∧
      x ^ 2 = Complex.normSq (psi 0) ∧
      darkState x y t = CStarMatrix.ofMatrix (outer psi) ∧
      darkRecordState x y t = CStarMatrix.ofMatrix
        (fun p q : O => if p.1 = false ∧ q.1 = false then outer psi p.2 q.2 else 0) := by
  let x := Real.sqrt (Complex.normSq (psi 0))
  let y := Real.sqrt (Complex.normSq (psi 1))
  let t := star (psi 0) * psi 1/(x * y : ℝ)
  have hx : 0 < x := Real.sqrt_pos.mpr ha
  have hy : 0 < y := Real.sqrt_pos.mpr (by linarith)
  have hxs : x ^ 2 = Complex.normSq (psi 0) := Real.sq_sqrt ha.le
  have hys : y ^ 2 = Complex.normSq (psi 1) := Real.sq_sqrt (by linarith)
  have hn : Complex.normSq t = 1 := by
    simp only [t, map_div₀, Complex.normSq_mul, Complex.normSq_conj, Complex.star_def,
      Complex.normSq_ofReal]
    rw [← hxs, ← hys]
    field_simp [hx.ne', hy.ne']
  have ht : star t * t = 1 := by
    change (starRingEnd ℂ) t * t = 1
    rw [← Complex.normSq_eq_conj_mul_self, hn]
    norm_num
  have hxy : x ^ 2 + y ^ 2 = 1 := by linarith
  have hxa : (x : ℂ) ^ 2 = star (psi 0) * psi 0 := by
    change (x : ℂ) ^ 2 = (starRingEnd ℂ) (psi 0) * psi 0
    rw [← Complex.normSq_eq_conj_mul_self, ← hxs]
    norm_cast
  have hya : (y : ℂ) ^ 2 = star (psi 1) * psi 1 := by
    change (y : ℂ) ^ 2 = (starRingEnd ℂ) (psi 1) * psi 1
    rw [← Complex.normSq_eq_conj_mul_self, ← hys]
    norm_cast
  have hxn : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hyn : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  simp only [Complex.star_def] at hxa hya
  have hd : darkState x y t = CStarMatrix.ofMatrix (outer psi) := by
    ext i j
    change (basisMatrix x y t * Matrix.single (0 : Q) 0 (1 : ℂ) * (basisMatrix x y t)ᴴ :
      Matrix Q Q ℂ) i j =
      psi i * star (psi j)
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
        basisMatrix, Matrix.single, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Complex.star_def, t] <;>
      norm_num <;>
      field_simp [hxn, hyn] <;>
      first
      | solve | ring
      | solve | linear_combination hxa
      | solve | linear_combination hya
      | linear_combination -(psi 1 * (starRingEnd ℂ) (psi 1)) * hxa
  have hr : darkRecordState x y t = CStarMatrix.ofMatrix
      (fun p q : O => if p.1 = false ∧ q.1 = false then outer psi p.2 q.2 else 0) := by
    ext ⟨s, i⟩ ⟨r, j⟩
    change (recordBasis (basisMatrix x y t) *
      Matrix.single (false, 0) (false, 0) (1 : ℂ) *
      (recordBasis (basisMatrix x y t))ᴴ : Matrix O O ℂ) (s, i) (r, j) =
        if s = false ∧ r = false then outer psi i j else 0
    have he := congrArg (fun M : CStarMatrix Q Q ℂ => M i j) hd
    cases s <;> cases r <;>
      simp [darkRecordState, recordBasis, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
        Matrix.single]
    simpa [darkState, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single] using he
  exact ⟨x, y, t, hxy, hx, hy, ht, hxs, hd, hr⟩

/-- The common reference-test lower bound for every original legal channel and
every pure dark state, with no restriction on its complex phase or Kraus representation. -/
theorem reference_lower_bound (F : QuantumChannel (Fin 2) (Bool × Fin 2))
    (psi : Fin 2 → ℂ) (z : ℝ)
    (hu : Complex.normSq (psi 0) + Complex.normSq (psi 1) = 1)
    (ha : 0 < Complex.normSq (psi 0)) (ha1 : Complex.normSq (psi 0) < 1)
    (hz : 1/2 ≤ z) (hz1 : z < 1)
    (hcond : 0 ≤ Complex.normSq (psi 0) + 2 * (1-2 * Complex.normSq (psi 0)) * z)
    (hfixed : ∀ i j : Fin 2, F.toCompletelyPositiveMap
      (CStarMatrix.ofMatrix (Matrix.vecMulVec psi (star psi))) (false, i) (false, j) =
        psi i * star (psi j)) :
    referenceLowerBound (Complex.normSq (psi 0)) z ≤ diamondDistance F nominalInstrument/2 := by
  have hunit : star psi ⬝ᵥ psi = 1 := by
    simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_add, hu, Complex.ofReal_one]
  let sigma := F.mapState (pureState psi hunit)
  let A : Matrix O O ℂ := CStarMatrix.ofMatrix.symm sigma.1
  have hpsd : A.PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm sigma.2.1)
  have hentry (i j : Q) : A (false, i) (false, j) = psi i * star (psi j) := hfixed i j
  have hfalse : (∑ i : Q, A (false, i) (false, i)) = 1 := by
    simp [hentry, Fin.sum_univ_two, Complex.star_def, Complex.mul_conj,
      ← Complex.ofReal_add, hu]
  have htrace : Matrix.trace A = 1 := sigma.2.2
  have hsum : (∑ i : Q, A (true, i) (true, i)) = 0 := by
    simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type, Fintype.sum_bool]
      at htrace
    linear_combination htrace-hfalse
  have hdiag (i : Q) : A (true, i) (true, i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hpsd.diag_nonneg)).mp hsum i
      (Finset.mem_univ i)
  have hcol (i : Q) (p : O) : A p (true, i) = 0 := by
    have hv := (hpsd.dotProduct_mulVec_zero_iff (Pi.single (true, i) (1 : ℂ))).mp
      (by simpa [Pi.star_single, Matrix.mulVec_single, single_dotProduct] using hdiag i)
    simpa [Matrix.mulVec_single] using congrFun hv p
  have hrow (i : Q) (p : O) : A (true, i) p = 0 := by
    simpa only [hcol, star_zero] using (hpsd.isHermitian.apply (true, i) p).symm
  have hfull : F.toCompletelyPositiveMap (CStarMatrix.ofMatrix (outer psi)) =
      CStarMatrix.ofMatrix
        (fun p q : O => if p.1 = false ∧ q.1 = false then outer psi p.2 q.2 else 0) := by
    ext ⟨s, i⟩ ⟨r, j⟩
    change A (s, i) (r, j) = if s = false ∧ r = false then psi i * star (psi j) else 0
    cases s <;> cases r <;> simp [hentry, hcol, hrow]
  obtain ⟨x, y, t, hxy, hx, hy, ht, hxs, hd, hr⟩ := phase_representation psi hu ha ha1
  rw [← hxs]
  apply reference_lower_bound_phase F x y z t hxy hx hy ht hz hz1
  · simpa only [hxs] using hcond
  · rw [hd, hr]
    exact hfull

end D5.S3.Quantum.Measurement.ArbitraryDarkReferenceLowerBound
