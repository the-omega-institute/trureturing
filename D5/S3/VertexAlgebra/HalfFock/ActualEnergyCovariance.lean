/- GID: D5/S3/VertexAlgebra/HalfFock/ActualEnergyCovariance
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/ActualEnergyCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Energy covariance of the original corrected all-source field. -/

import D5.S3.VertexAlgebra.HalfFock.ActualCorrCovariance
import D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
import D5.S3.VertexAlgebra.LatticeHalfFockGradedTrace
import D5.S3.VertexAlgebra.LatticeEnergyGrading

/-!
Classical twisted lattice grading, with the original tensor zero mode, normal
word field and finite Corr. The mode sum is finite only after application to
an input. In particular, this proof does not sum endomorphisms over all modes.
Source weights are r+1, whereas twisted oscillator weights are 2r+1.
No positivity, finite-dimensional grade, transpose, inversion or Jacobi law
is a premise.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.HalfFock.ActualEnergyCovariance

open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockChargedCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockFiniteCorrection
open LatticeHalfFockCorrectedField LatticeHalfFockGradedTrace
open LatticePositiveEnergy MvPolynomial

/-- Coefficient extraction in the original native field space. -/
private def coefficient (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ) :
    NativeField D hu →ₗ[ℂ] Module.End ℂ (ActualTensor D hu) where
  toFun F := F.coeff e
  map_add' F G := by
    apply LinearMap.ext
    intro x
    change ((HahnModule.of ℂ).symm (F x + G x)).coeff e = _
    simp only [HahnModule.of_symm_add, HahnSeries.coeff_add,
      LinearMap.add_apply, HVertexOperator.coeff_apply_apply]
  map_smul' c F := by
    apply LinearMap.ext
    intro x
    change ((HahnModule.of ℂ).symm (c • F x)).coeff e = _
    simp only [HahnModule.of_symm_smul, HahnSeries.coeff_smul,
      LinearMap.smul_apply, RingHom.id_apply, HVertexOperator.coeff_apply_apply]

private def zeroBracket (D : LatticeData) (hu : IsUnit D.G.det) :
    Module.End ℂ (ActualTensor D hu) →ₗ[ℂ] Module.End ℂ (ActualTensor D hu) where
  toFun A := actualTensorL0 D hu * A - A * actualTensorL0 D hu
  map_add' A B := by simp only [mul_add, add_mul]; abel
  map_smul' c A := by
    simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub,
      RingHom.id_apply]

private theorem zeroBracket_mul (D : LatticeData) (hu : IsUnit D.G.det)
    (A B : Module.End ℂ (ActualTensor D hu)) :
    zeroBracket D hu (A * B) = zeroBracket D hu A * B + A * zeroBracket D hu B := by
  change actualTensorL0 D hu * (A * B) - (A * B) * actualTensorL0 D hu =
    (actualTensorL0 D hu * A - A * actualTensorL0 D hu) * B +
      A * (actualTensorL0 D hu * B - B * actualTensorL0 D hu)
  noncomm_ring

private theorem jetCurrent_bracket (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Index D) (k : ℤ) :
    zeroBracket D hu (jetCurrent D hu i k) = -frequency k • jetCurrent D hu i k := by
  change zeroBracket D hu
    (jetScalar i.2 k • tensorCurrent D (ActualGround D hu) i.1 k) = _
  rw [map_smul]
  have h := LatticeHalfFockChargedLZero.tensor_current_L_zero_commutator D hu i.1 k
  change zeroBracket D hu (tensorCurrent D (ActualGround D hu) i.1 k) = _ at h
  rw [h]
  exact smul_comm _ _ _

/-- Both normal ordering branches have the same displacement. The current
contributes -k-1/2 and the shifted tail contributes k+r+3/2. -/
private theorem flatCoefficient_bracket (D : LatticeData) (hu : IsUnit D.G.det)
    (q : Charge D) (w : List (Index D)) (m : ModeTuple D w) (e : ℤ) :
    zeroBracket D hu (flatCoefficient D hu (chargedField D hu q) w m e) =
      ((((e + bilinear D q q : ℤ) : ℂ) / 2) + (wordWeight D w : ℂ)) •
        flatCoefficient D hu (chargedField D hu q) w m e := by
  induction w generalizing e with
  | nil =>
    simp only [flatCoefficient, chargedField, HVertexOperator.coeff_of_coeff,
      wordWeight, List.map_nil, List.sum_nil, Nat.cast_zero, add_zero]
    change actualTensorL0 D hu * chargedCoefficient D hu q e -
      chargedCoefficient D hu q e * actualTensorL0 D hu = _
    exact LatticeHalfFockChargedLZero.charged_tensor_L_zero_commutator D hu q e
  | cons i w ih =>
    simp only [flatCoefficient]
    split_ifs with hk
    · rw [zeroBracket_mul, jetCurrent_bracket, ih]
      simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← add_smul]
      congr 1
      simp only [frequency, wordWeight, List.map_cons, List.sum_cons, sourceWeight,
        Nat.cast_add, Nat.cast_one]
      push_cast
      ring
    · rw [zeroBracket_mul, ih, jetCurrent_bracket]
      simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← add_smul]
      congr 1
      simp only [frequency, wordWeight, List.map_cons, List.sum_cons, sourceWeight,
        Nat.cast_add, Nat.cast_one]
      push_cast
      ring

/-- L0 passes through the pointwise mode sum using finite support at x and
L0 x separately; no End-valued finite-support assertion occurs. -/
private theorem wordField_bracket (D : LatticeData) (hu : IsUnit D.G.det)
    (q : Charge D) (w : List (Index D)) (e : ℤ) :
    zeroBracket D hu (coefficient D hu e (wordField D hu (chargedField D hu q) w)) =
      ((((e + bilinear D q q : ℤ) : ℂ) / 2) + (wordWeight D w : ℂ)) •
        coefficient D hu e (wordField D hu (chargedField D hu q) w) := by
  apply LinearMap.ext
  intro x
  change actualTensorL0 D hu ((wordField D hu (chargedField D hu q) w).coeff e x) -
      (wordField D hu (chargedField D hu q) w).coeff e (actualTensorL0 D hu x) =
    (((((e + bilinear D q q : ℤ) : ℂ) / 2) + (wordWeight D w : ℂ)) : ℂ) •
      (wordField D hu (chargedField D hu q) w).coeff e x
  simp only [wordField_coefficient]
  have hx := flatTerm_finite D hu (chargedField D hu q) w e x
  have hLx := flatTerm_finite D hu (chargedField D hu q) w e (actualTensorL0 D hu x)
  rw [map_finsum _ hx,
    ← finsum_sub_distrib (hx.fun_comp (map_zero (actualTensorL0 D hu))) hLx,
    smul_finsum' _ hx]
  apply finsum_congr
  intro m
  exact LinearMap.congr_fun (flatCoefficient_bracket D hu q w m e) x

private theorem polynomial_monomial_bracket (D : LatticeData) (hu : IsUnit D.G.det)
    (q : Charge D) (m : Index D →₀ ℕ) (c : ℂ) (e : ℤ) :
    zeroBracket D hu (coefficient D hu e (polynomialField D hu q (monomial m c))) =
      ((((e + bilinear D q q : ℤ) : ℂ) / 2) +
        (Finsupp.weight (sourceWeight D) m : ℂ)) •
      coefficient D hu e (polynomialField D hu q (monomial m c)) := by
  have hm : monomial m c = c • monomial m (1 : ℂ) := by
    simp only [smul_monomial, smul_eq_mul, mul_one]
  simp only [hm, map_smul, polynomialField_monomial_public]
  rw [wordField_bracket]
  have hw : wordWeight D (LatticeHalfFockFockNormalField.occurrences D m) =
      Finsupp.weight (sourceWeight D) m := wordWeight_occurrences D m
  rw [hw]
  exact smul_comm _ _ _

/-- Corr's exact bidegree cancels its original shift e+2s, on every
monomial of every coefficient of an arbitrary homogeneous polynomial. -/
private theorem correctedPolynomial_bracket (D : LatticeData) (hu : IsUnit D.G.det)
    (q : Charge D) (p : Oscillator D) (R : ℕ)
    (hp : IsWeightedHomogeneous (sourceWeight D) p R) (e : ℤ) :
    zeroBracket D hu (coefficient D hu e (correctedPolynomial D hu q p)) =
      ((e : ℂ) / 2 + ((chargeEnergy D q : ℤ) : ℂ) + (R : ℂ)) •
        coefficient D hu e (correctedPolynomial D hu q p) := by
  classical
  have hexp : coefficient D hu e (correctedPolynomial D hu q p) =
      ∑ s ∈ (Corr D q p).support, coefficient D hu (e + 2 * (s : ℤ))
        (polynomialField D hu q (Corr D q p s)) := by
    change coefficient D hu e
      ((Finsupp.lsum ℂ (fun s : ℕ =>
        (shiftField D hu s).comp (polynomialField D hu q))) (Corr D q p)) = _
    rw [Finsupp.lsum_apply]
    simp only [Finsupp.sum, LinearMap.comp_apply, map_sum]
    apply Finset.sum_congr rfl
    intro s hs
    exact shiftField_coefficient_public D hu s
      (polynomialField D hu q (Corr D q p s)) e
  simp only [hexp, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hmexp := congrArg (fun p' : Oscillator D =>
    coefficient D hu (e + 2 * (s : ℤ)) (polynomialField D hu q p'))
      (MvPolynomial.as_sum (Corr D q p s))
  simp only [map_sum] at hmexp
  simp only [hmexp, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [polynomial_monomial_bracket]
  have hb := ActualCorrCovariance.Corr_coefficient_bidegree D q p R hp s m
    (MvPolynomial.mem_support_iff.mp hm)
  have hq := congrArg (fun z : ℤ => (z : ℂ)) (two_chargeEnergy D q)
  have hw := congrArg (fun z : ℕ => (z : ℂ)) hb
  push_cast at hq hw ⊢
  congr 1
  linear_combination -hq / 2 + hw

private def coefficientDefect (D : LatticeData) (hu : IsUnit D.G.det) (e h : ℤ) :
    Carrier D →ₗ[ℂ] Module.End ℂ (ActualTensor D hu) :=
  (zeroBracket D hu).comp ((coefficient D hu e).comp (correctedField D hu)) -
    ((e : ℂ) / 2 + (h : ℂ)) • ((coefficient D hu e).comp (correctedField D hu))

/-- The ORIGINAL corrected field obeys the all-source zero-mode law on
the full integer energy grade. Generic indefinite lattices are included. -/
theorem correctedField_L_zero_commutator (D : LatticeData) (hu : IsUnit D.G.det)
    (h : ℤ) (a : Carrier D) (ha : a ∈ grade D h) (e : ℤ) :
    actualTensorL0 D hu * (correctedField D hu a).coeff e -
      (correctedField D hu a).coeff e * actualTensorL0 D hu =
        ((e : ℂ) / 2 + (h : ℂ)) • (correctedField D hu a).coeff e := by
  have hker : grade D h ≤ LinearMap.ker (coefficientDefect D hu e h) := by
    rw [grade_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨q, m⟩, he, rfl⟩
    change coefficientDefect D hu e h (carrierBasis D (q, m)) = 0
    change zeroBracket D hu (coefficient D hu e
        (correctedField D hu (carrierBasis D (q, m)))) -
      ((e : ℂ) / 2 + (h : ℂ)) • coefficient D hu e
        (correctedField D hu (carrierBasis D (q, m))) = 0
    rw [carrierBasis_apply]
    simp only [correctedField, Finsupp.lsum_single]
    rw [correctedPolynomial_bracket D hu q (monomial m 1)
      (Finsupp.weight (sourceWeight D) m)
      (isWeightedHomogeneous_monomial _ _ _ rfl)]
    have hh : chargeEnergy D q + (Finsupp.weight (sourceWeight D) m : ℤ) = h := he
    have hc := congrArg (fun z : ℤ => (z : ℂ)) hh
    push_cast at hc
    have hs : (e : ℂ) / 2 + (chargeEnergy D q : ℂ) +
        (Finsupp.weight (sourceWeight D) m : ℂ) = (e : ℂ) / 2 + (h : ℂ) := by
      linear_combination hc
    rw [hs, sub_self]
  exact sub_eq_zero.mp (hker ha)

/-- The output grade is signed. In particular a negative output index is
never truncated to a nonnegative degree. -/
theorem correctedField_signed_output (D : LatticeData) (hu : IsUnit D.G.det)
    (h M e : ℤ) (a : Carrier D) (ha : a ∈ grade D h) (x : ActualTensor D hu)
    (hx : actualTensorL0 D hu x = ((D.rank : ℂ) / 16 + (M : ℂ) / 2) • x) :
    actualTensorL0 D hu ((correctedField D hu a).coeff e x) =
      ((D.rank : ℂ) / 16 + ((M + e + 2 * h : ℤ) : ℂ) / 2) •
        (correctedField D hu a).coeff e x := by
  have hc := LinearMap.congr_fun (correctedField_L_zero_commutator D hu h a ha e) x
  change actualTensorL0 D hu ((correctedField D hu a).coeff e x) -
    (correctedField D hu a).coeff e (actualTensorL0 D hu x) =
    ((e : ℂ) / 2 + (h : ℂ)) • (correctedField D hu a).coeff e x at hc
  rw [hx, map_smul] at hc
  rw [sub_eq_iff_eq_add] at hc
  rw [hc, ← add_smul]
  congr 1
  push_cast
  ring

end D5.S3.VertexAlgebra.HalfFock.ActualEnergyCovariance

#print axioms D5.S3.VertexAlgebra.HalfFock.ActualEnergyCovariance.correctedField_L_zero_commutator

#print axioms D5.S3.VertexAlgebra.HalfFock.ActualEnergyCovariance.correctedField_signed_output
