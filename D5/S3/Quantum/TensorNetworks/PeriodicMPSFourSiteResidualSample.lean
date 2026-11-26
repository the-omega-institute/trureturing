/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualSample
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualSample
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Homogeneous residual identities for a four-site pencil specialization. -/

import D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteSextic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ReduceModChar
import Mathlib.Algebra.CharP.Defs
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.CharP.Algebra
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Four low-degree reductions for the residual system of the specialized pencil. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteResidualSample

variable {R : Type*} [CommRing R]

private def cubic (x y z : R) : R :=
  -2 * x ^ 2 * y + x ^ 2 * z + x * y ^ 2 + 2 * y ^ 3 - 2 * y ^ 2 * z - 2 * z ^ 3

private def quad (x y z : R) : R :=
  x * y - 2 * x * z - y ^ 2 - 2 * y * z

private def quartic (x y z : R) : R :=
  x ^ 3 * y - x ^ 3 * z - x ^ 2 * y ^ 2 - x ^ 2 * y * z - 2 * x * y ^ 3 +
    2 * x * y ^ 2 * z - x * y * z ^ 2 - 2 * x * z ^ 3 - 2 * y ^ 3 * z

variable [CharP R 5]

private lemma five_eq_zero : (5 : R) = 0 := CharP.cast_eq_zero R 5

private lemma cubic_reduction (x y z : R) :
    2 * x ^ 2 * z - 2 * x * z ^ 2 + y ^ 3 - 2 * y * z ^ 2 - 2 * z ^ 3 =
      cubic x y z + (2 * x + y + z) * quad x y z := by
  unfold cubic quad
  linear_combination (x ^ 2 * z + x * y * z + y ^ 2 * z) * (five_eq_zero (R := R))

private lemma quartic_reduction (x y z : R) :
    x ^ 3 * z + 2 * x * z ^ 3 - y ^ 2 * z ^ 2 - y * z ^ 3 + 2 * z ^ 4 =
      (x ^ 2 + 2 * x * y + 2 * x * z - y ^ 2 + y * z + z ^ 2) * quad x y z +
        (-2 * x + 2 * y - z) * cubic x y z := by
  unfold cubic quad
  linear_combination
    (-x ^ 3 * y + x ^ 3 * z + x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + x * y ^ 3 +
      x * y * z ^ 2 - y ^ 4 + y ^ 3 * z + y * z ^ 3) * (five_eq_zero (R := R))

private lemma sixth_reduction (x y z : R) :
    z ^ 6 = (x * y - x ^ 2) * quartic x y z +
      (2 * x ^ 4 + x * y ^ 3 - x * y ^ 2 * z - 2 * x * y * z ^ 2 +
        x * z ^ 3 - 2 * y ^ 2 * z ^ 2 + z ^ 4) * quad x y z +
      (-2 * x ^ 3 - x ^ 2 * y - 2 * x * y ^ 2 + 2 * x * y * z -
        x * z ^ 2 - y * z ^ 2 + 2 * z ^ 3) * cubic x y z := by
  unfold cubic quad quartic
  linear_combination
    (-x ^ 5 * y + x ^ 5 * z + x ^ 4 * y * z + x ^ 3 * y ^ 2 * z -
      x ^ 3 * y * z ^ 2 - x ^ 3 * z ^ 3 + x ^ 2 * y ^ 4 - x ^ 2 * y ^ 3 * z +
      x * y ^ 5 - x * y ^ 4 * z + x * y ^ 3 * z ^ 2 - 3 * x * y ^ 2 * z ^ 3 +
      x * y * z ^ 4 - 2 * y ^ 3 * z ^ 3 + y ^ 2 * z ^ 4 + z ^ 6) * (five_eq_zero (R := R))

private def monomialValue (x y z : R) (a b c : ℕ) : R := x ^ a * y ^ b * z ^ c

/-- In the residual system the only potentially nonzero monomial of total degree eight
is the eighth power of the first coordinate. This also applies in the quotient ring. -/
theorem degree_eight_monomial_vanishes (x y z : R)
    (hc : cubic x y z = 0) (hq : quad x y z = 0) (hr : quartic x y z = 0)
    (a b c : ℕ) (hdegree : a + b + c = 8) (hother : 0 < b + c) :
    x ^ a * y ^ b * z ^ c = 0 := by
  have hz : z ^ 6 = 0 := by
    simpa only [hc, hq, hr, mul_zero, add_zero] using sixth_reduction x y z
  have hxy : x * y - 2 * x * z - y ^ 2 - 2 * y * z = 0 := hq
  have hy3 : 2 * x ^ 2 * z - 2 * x * z ^ 2 + y ^ 3 - 2 * y * z ^ 2 - 2 * z ^ 3 = 0 := by
    simpa only [hc, hq, mul_zero, add_zero] using cubic_reduction x y z
  have hx3z : x ^ 3 * z + 2 * x * z ^ 3 - y ^ 2 * z ^ 2 - y * z ^ 3 + 2 * z ^ 4 = 0 := by
    simpa only [hc, hq, mul_zero, add_zero] using quartic_reduction x y z
  let m := monomialValue x y z
  change m a b c = 0
  suffices main : ∀ n a b c : ℕ, 5 * a + 4 * b + c = n → a + b + c = 8 →
      0 < b + c → m a b c = 0 from main _ a b c rfl hdegree hother
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b c hw hd hn
    have lower (a' b' c' : ℕ) (hw' : 5 * a' + 4 * b' + c' < n)
        (hd' : a' + b' + c' = 8) (hn' : 0 < b' + c') : m a' b' c' = 0 :=
      ih _ hw' a' b' c' rfl hd' hn'
    by_cases hz6 : 6 ≤ c
    · obtain ⟨c', rfl⟩ := Nat.exists_eq_add_of_le hz6
      simp [m, monomialValue, pow_add, hz]
    by_cases hy3' : 3 ≤ b
    · obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hy3'
      have t₁ := lower (a+2) b' (c+1) (by omega) (by omega) (by omega)
      have t₂ := lower (a+1) b' (c+2) (by omega) (by omega) (by omega)
      have t₃ := lower a (b'+1) (c+2) (by omega) (by omega) (by omega)
      have t₄ := lower a b' (c+3) (by omega) (by omega) (by omega)
      simp only [m, monomialValue, pow_add, pow_one] at t₁ t₂ t₃ t₄ ⊢
      linear_combination (x ^ a * y ^ b' * z ^ c) * hy3 - 2 * t₁ + 2 * t₂ + 2 * t₃ + 2 * t₄
    by_cases hx3z' : 3 ≤ a ∧ 1 ≤ c
    · obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le hx3z'.1
      obtain ⟨c', rfl⟩ := Nat.exists_eq_add_of_le hx3z'.2
      have t₁ := lower (a'+1) b (c'+3) (by omega) (by omega) (by omega)
      have t₂ := lower a' (b+2) (c'+2) (by omega) (by omega) (by omega)
      have t₃ := lower a' (b+1) (c'+3) (by omega) (by omega) (by omega)
      have t₄ := lower a' b (c'+4) (by omega) (by omega) (by omega)
      simp only [m, monomialValue, pow_add, pow_one] at t₁ t₂ t₃ t₄ ⊢
      linear_combination (x ^ a' * y ^ b * z ^ c') * hx3z - 2 * t₁ + t₂ + t₃ - 2 * t₄
    have hab : 1 ≤ a ∧ 1 ≤ b := by omega
    obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le hab.1
    obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hab.2
    have t₁ := lower (a'+1) b' (c+1) (by omega) (by omega) (by omega)
    have t₂ := lower a' (b'+2) c (by omega) (by omega) (by omega)
    have t₃ := lower a' (b'+1) (c+1) (by omega) (by omega) (by omega)
    simp only [m, monomialValue, pow_add, pow_one] at t₁ t₂ t₃ ⊢
    linear_combination (x ^ a' * y ^ b' * z ^ c) * hxy + 2 * t₁ + t₂ + 2 * t₃

/-- Evaluation of any degree-eight polynomial on the sample residual equations lies
in the line generated by the eighth power of the first variable. -/
theorem degree_eight_polynomial_image {K : Type*} [Field K] [Algebra K R]
    (x y z : R) (hc : cubic x y z = 0) (hq : quad x y z = 0) (hr : quartic x y z = 0)
    (polynomial : MvPolynomial (Fin 3) K) (hdegree : polynomial.IsHomogeneous 8) :
    ∃ c : K, MvPolynomial.aeval ![x, y, z] polynomial = c • x ^ 8 := by
  classical
  let read : MvPolynomial (Fin 3) K →ₐ[K] R := MvPolynomial.aeval ![x, y, z]
  have hmonomial (d : Fin 3 →₀ ℕ) (hd : d ∈ polynomial.support) :
      read (MvPolynomial.monomial d (polynomial.coeff d)) =
        (if d 1 + d 2 = 0 then polynomial.coeff d else 0) • x ^ 8 := by
    have hw : d.degree = 8 := by
      rw [Finsupp.degree_eq_weight_one]
      exact hdegree (MvPolynomial.mem_support_iff.mp hd)
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_three] at hw
    dsimp only [read]
    rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rw [Fin.prod_univ_three]
    change (algebraMap K R) (polynomial.coeff d) * (x ^ d 0 * y ^ d 1 * z ^ d 2) = _
    by_cases hs : d 1 + d 2 = 0
    · rw [ite_eq_left hs, show d 0 = 8 by omega, show d 1 = 0 by omega, show d 2 = 0 by omega,
        pow_zero, pow_zero, mul_one, mul_one, Algebra.smul_def]
    · rw [ite_eq_right hs, zero_smul,
        degree_eight_monomial_vanishes x y z hc hq hr (d 0) (d 1) (d 2)
          (by omega) (by omega), mul_zero]
  refine ⟨∑ d ∈ polynomial.support, if d 1 + d 2 = 0 then polynomial.coeff d else 0, ?_⟩
  change read polynomial = _
  nth_rw 1 [polynomial.as_sum]
  rw [map_sum, Finset.sum_smul]
  exact Finset.sum_congr rfl hmonomial

open MvPolynomial in
/-- The homogeneous residual equations of the characteristic-five sample. -/
noncomputable def residualIdeal (K : Type*) [Field K] : Ideal (MvPolynomial (Fin 3) K) :=
  Ideal.span {cubic (X 0) (X 1) (X 2), quad (X 0) (X 1) (X 2),
    quartic (X 0) (X 1) (X 2)}

set_option maxHeartbeats 900000 in
-- Checking the quotient algebra and the induced linear map uses extra elaboration.
open MvPolynomial in
/-- The degree-eight piece of the residual quotient has dimension at most one. -/
theorem residual_sample_degree_eight_rank (K : Type*) [Field K] [CharP K 5] :
    Module.finrank K (LinearMap.range
      ((Ideal.Quotient.mkₐ K (residualIdeal K)).toLinearMap.comp
        (homogeneousSubmodule (Fin 3) K 8).subtype)) ≤ 1 := by
  let S := MvPolynomial (Fin 3) K
  let I := residualIdeal K
  let A := S ⧸ I
  let q : S →ₐ[K] A := Ideal.Quotient.mkₐ K I
  let r : homogeneousSubmodule (Fin 3) K 8 →ₗ[K] A :=
    q.toLinearMap.comp (homogeneousSubmodule (Fin 3) K 8).subtype
  change Module.finrank K (LinearMap.range r) ≤ 1
  let sampleRead : S →+* K := eval (![1, 0, 0] : Fin 3 → K)
  have hx0 : sampleRead (X 0) = 1 := eval_X _
  have hx1 : sampleRead (X 1) = 0 := eval_X _
  have hx2 : sampleRead (X 2) = 0 := eval_X _
  have hmem : I ≤ RingHom.ker sampleRead := by
    apply Ideal.span_le.mpr
    intro polynomial h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    change polynomial ∈ RingHom.ker sampleRead
    apply RingHom.mem_ker.mpr
    change sampleRead polynomial = 0
    rcases h with rfl | rfl | rfl <;>
      simp [cubic, quad, quartic, map_ofNat, hx0, hx1, hx2]
  let : Nontrivial A := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (RingHom.ker_ne_top sampleRead) hmem)
  let : CharP A 5 := charP_of_injective_algebraMap (algebraMap K A).injective 5
  have htwo : q (2 : S) = 2 := map_ofNat q 2
  let x := q (X 0)
  let y := q (X 1)
  let z := q (X 2)
  have hqzero (p : S) (hp : p ∈ I) : q p = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hp
  have hc : cubic x y z = 0 := by
    simpa [x, y, z, cubic, htwo] using
      hqzero (cubic (X 0) (X 1) (X 2)) (Ideal.subset_span (by simp))
  have hq : quad x y z = 0 := by
    simpa [x, y, z, quad, htwo] using
      hqzero (quad (X 0) (X 1) (X 2)) (Ideal.subset_span (by simp))
  have hr : quartic x y z = 0 := by
    simpa [x, y, z, quartic, htwo] using
      hqzero (quartic (X 0) (X 1) (X 2)) (Ideal.subset_span (by simp))
  have hpower : (X (0 : Fin 3) ^ 8 : S).IsHomogeneous 8 := by
    rw [X_pow_eq_monomial]
    exact isHomogeneous_monomial 1 (by simp)
  let first : homogeneousSubmodule (Fin 3) K 8 := ⟨X 0 ^ 8, hpower⟩
  let firstImage : LinearMap.range r := ⟨r first, LinearMap.mem_range_self r first⟩
  refine finrank_le_one firstImage ?_
  intro w
  obtain ⟨p, hp⟩ := w.property
  obtain ⟨c, he⟩ := degree_eight_polynomial_image x y z hc hq hr p.val p.property
  have heq : aeval (![x, y, z] : Fin 3 → A) = q := by
    ext t
    rw [aeval_X]
    fin_cases t <;> rfl
  rw [heq] at he
  refine ⟨c, Subtype.ext ?_⟩
  change c • r first = w.val
  rw [← hp]
  change c • q (X 0 ^ 8) = q p.val
  rw [map_pow]
  exact he.symm

/-- Over any field of characteristic five, the residual system of the sample
has just the first coordinate point in projective space. -/
theorem residual_sample_unique {K : Type*} [Field K] [CharP K 5] (x y z : K)
    (hc : cubic x y z = 0) (hq : quad x y z = 0) (hr : quartic x y z = 0) :
    y = 0 ∧ z = 0 := by
  have hz : z = 0 := eq_zero_of_pow_eq_zero (by
    simpa only [hc, hq, hr, mul_zero, add_zero] using sixth_reduction x y z)
  have hcube : y ^ 3 = 0 := by
    have h := cubic_reduction x y z
    rw [hc, hq, mul_zero, add_zero, hz] at h
    simpa using h
  exact ⟨eq_zero_of_pow_eq_zero hcube, hz⟩

section SamplePencils

open PeriodicMPSFourSiteSextic (sextic sextic_square_and_triplet)

private abbrev F5 := ZMod 5

private def partnerCoordinates (x y z : R) : Fin 3 → R :=
  ![x ^ 2 + x * y - 2 * x * z - y ^ 2 - 2 * y * z,
    -x * y - y ^ 2 - y * z + 2 * z ^ 2,
    -x * z + y ^ 2 + y * z - z ^ 2]

private def tripletDet (x y z : R) : R :=
  x ^ 3 + x ^ 2 * y - 2 * x ^ 2 * z - x * y ^ 2 + x * y * z - x * z ^ 2 +
    y ^ 3 + y ^ 2 * z - y * z ^ 2 + z ^ 3

private def leftSinglet (x y z : R) : R := 2 * x + y + 3 * z

private def rightSinglet (x y : R) : R := 2 * x + 2 * y

private def rightConic (x y z : R) : R := -x * y + x * z + y ^ 2 + z ^ 2

private def leftSampleSextic (x y z : R) : R :=
  sextic (2 * x + 4 * z) (3 * x + 3 * z) (4 * x + 3 * y + 4 * z)
    (x + 4 * y + 2 * z) (2 * x + 3 * y) (x + y + 3 * z)

private def rightSampleSextic (x y z : R) : R :=
  sextic (2 * x + 3 * z) (2 * y + 2 * z) (x + 4 * y + z)
    (3 * x + y + z) (4 * y + 3 * z) (4 * x)

set_option maxHeartbeats 900000 in
-- The two degree-six expansions require more heartbeats than the default.
/-- At the sample, the left sextic decomposes into the cubic product constraint and
the determinant divisor times the left conic. The right pencil has the same identity. -/
theorem sample_pencil_decompositions (x y z : R) :
    let partner := partnerCoordinates x y z
    let d := tripletDet x y z
    let f := leftSinglet x y z
    let g := rightSinglet x y
    let leftCofactor :=
      x ^ 3 - x ^ 2 * y - x * y ^ 2 - x * y * z + x * z ^ 2 +
        2 * y ^ 3 + 2 * y * z ^ 2 - z ^ 3
    let rightCofactor :=
      x ^ 3 - 2 * x ^ 2 * y + 2 * x ^ 2 * z + 2 * x * y ^ 2 + x * y * z -
        2 * y ^ 3 + y ^ 2 * z - z ^ 3
    f * rightSinglet (partner 0) (partner 1) - 4 * d = cubic x y z ∧
    leftSampleSextic x y z = f * d * quad x y z + cubic x y z * leftCofactor ∧
    rightSampleSextic x y z =
      g * d * rightConic x y z +
        (g * leftSinglet (partner 0) (partner 1) (partner 2) - 4 * d) * rightCofactor ∧
    rightConic (partner 0) (partner 1) (partner 2) = quartic x y z := by
  have hp0 : partnerCoordinates x y z 0 = x ^ 2 + x * y - 2 * x * z - y ^ 2 - 2 * y * z := rfl
  have hp1 : partnerCoordinates x y z 1 = -x * y - y ^ 2 - y * z + 2 * z ^ 2 := rfl
  have hp2 : partnerCoordinates x y z 2 = -x * z + y ^ 2 + y * z - z ^ 2 := rfl
  dsimp only
  simp only [hp0, hp1, hp2, leftSinglet, rightSinglet, tripletDet, leftSampleSextic,
    rightSampleSextic, rightConic, cubic, quad, quartic, sextic_square_and_triplet,
    PeriodicMPSFourSiteSextic.hankelDet]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring_nf <;> reduce_mod_char! <;> ring_nf <;> reduce_mod_char!

open scoped Matrix

private def sampleNecklaces (A B : Matrix (Fin 2) (Fin 2) F5) : Fin 6 → F5 :=
  ![(A ^ 4).trace, (A ^ 3 * B).trace, (A ^ 2 * B ^ 2).trace,
    ((A * B) ^ 2).trace, (A * B ^ 3).trace, (B ^ 4).trace]

private def sampleTriplet (f : Fin 6 → F5) : Matrix (Fin 3) (Fin 3) F5 :=
  !![f 0, 2 * f 1, f 2; f 1, f 2 + f 3, f 4; f 2, 2 * f 4, f 5]

private def leftTensors : Fin 2 → Matrix (Fin 2) (Fin 2) F5 :=
  ![!![4, 2; 1, 0], !![1, 3; 3, 2]]

private def rightTensors : Fin 2 → Matrix (Fin 2) (Fin 2) F5 :=
  ![!![4, 4; 2, 1], !![3, 2; 4, 3]]

/-- The specialization uses the two actual necklace vectors of the displayed tensors. -/
theorem sample_necklace_values :
    sampleNecklaces (leftTensors 0) (leftTensors 1) = ![2, 3, 4, 1, 2, 1] ∧
      sampleNecklaces (rightTensors 0) (rightTensors 1) = ![2, 0, 1, 3, 0, 4] := by
  decide +kernel

private def leftOrigin : Matrix (Fin 3) (Fin 3) F5 :=
  sampleTriplet (sampleNecklaces (leftTensors 0) (leftTensors 1))

private def rightOrigin : Matrix (Fin 3) (Fin 3) F5 :=
  sampleTriplet (sampleNecklaces (rightTensors 0) (rightTensors 1))

private def productTriplet : Matrix (Fin 3) (Fin 3) F5 := leftOrigin * rightOrigin

/-- The triplet pencil generators are the products of the actual sample triplets
with the first two powers of their common product. -/
theorem sample_pencil_generator_values :
    productTriplet = !![3, 4, 3; 3, 0, 1; 4, 1, 3] ∧
    productTriplet * leftOrigin = sampleTriplet ![0, 0, 3, 4, 3, 1] ∧
    productTriplet ^ 2 * leftOrigin = sampleTriplet ![4, 3, 4, 2, 0, 3] ∧
    rightOrigin * productTriplet = sampleTriplet ![0, 2, 4, 1, 4, 0] ∧
    rightOrigin * productTriplet ^ 2 = sampleTriplet ![3, 2, 1, 1, 3, 0] := by
  decide +kernel

end SamplePencils

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteResidualSample
