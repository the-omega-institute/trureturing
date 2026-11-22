/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalSectionRank
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalSectionRank
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Generic rank certificates on the paired vertical section. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalSectionTrace

/-! Determinant and rank certificates on the paired vertical section. -/

open Matrix MvPolynomial
open scoped Matrix Kronecker

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformVerticalSectionRank

noncomputable section

open PeriodicMPSUniformHardCoreTransferRecurrence (TwoBits binaryInsertion binaryTransfer)
open PeriodicMPSUniformAntisymmetricTransfer (mixedTransfer mixedRaw)
open PeriodicMPSUniformVerticalMiddle
  (BondMatrix sectionB0 sectionB1 sectionTransfer sectionTransfer_pow literalCross literalCross_eq
    completeSeries
    tripletFeature traceFeatures middleTraceBlock middleFactor)

variable {R : Type*} [CommRing R]

open PeriodicMPSUniformVerticalSection (outerRows outerDividedMatrix outerDividedDet)
open private featurePowers liftCore lowerFeatures outerEntry pairedBra upperFeatures from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalSectionTrace

section Determinants

open TrivSqZeroExt (inl inr snd)
open PeriodicMPSUniformAntisymmetricTransfer (commutatorDet coreCommutator)

variable {K : Type*} [Field K]

/-- The two off-diagonal generators of the action on the symmetric two-site
words. The bra action contributes the negative transpose of the opposite
generator. -/
def tripletShear (upper : Bool) : Matrix (Fin 3) (Fin 3) R :=
  if upper then !![0, 2, 0; 0, 0, 1; 0, 0, 0] else !![0, 0, 0; 1, 0, 0; 0, 2, 0]

def tripletRotation (upper : Bool) (F : Matrix (Fin 3) (Fin 3) R) :
    Matrix (Fin 3) (Fin 3) R :=
  tripletShear upper * F - F * (tripletShear (!upper)).transpose

private theorem section_rotation_middle (half : R) (B0 B1 : BondMatrix R) (m : ℕ)
    (upper : Bool) (j : Fin 3) :
    tripletRotation upper (tripletReadout half (transverseKet 0) (pairedBra B0 B1) m) 1 j =
      (tripletFeature half B0 B1 j * (if upper then B1 else B0) ^ m).trace := by
  cases upper <;> simp [tripletRotation, tripletShear, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_three, tripletReadout_section]

local notation "P" => MvPolynomial (Fin 5) K

private def sectionBra (x : Fin 5 → R) : Fin 2 → BondMatrix R :=
  pairedBra (sectionB0 (x 0) (x 1))
    (sectionB1 (x 2) (x 3) (x 3 + (x 2 - x 3) * x 4))

private def literalOuterColumn (a : K) (m : ℕ) : Matrix (Fin 6) (Fin 6) P :=
  Matrix.of fun i =>
    let F := outerEntry
      (tripletReadout (C a) (transverseKet 0) (sectionBra X) m) i
    ![pderiv 0 F, pderiv 1 F, pderiv 2 F, pderiv 3 F, pderiv 4 F,
      C ((![0, 2, 4, -4, -2, 0] : Fin 6 → ℤ) i : K) * F]

private theorem literalOuterColumn_eq (a : K) (ha : a + a = 1) (m : ℕ) :
    literalOuterColumn a m = outerDividedMatrix m := by
  have h (i : Fin 6) :
      outerEntry (tripletReadout (C a) (transverseKet 0) (sectionBra X) m) i =
        outerRows m i :=
    literalOuter_eq (C a) (by rw [← map_add, ha, map_one]) m i
  ext i j
  rw [literalOuterColumn, Matrix.of_apply, h]
  rfl

/-- The nine-row minor on the triplet readout. Its five polynomial partials
are taken before specialization. The omitted lower-left block vanishes
because the middle triplet row vanishes along the whole section, and the
diagonal physical generator preserves each triplet weight. -/
def sectionTripletMinor [Algebra K R] (a : K) (m : ℕ) (x : Fin 5 → R) :
    Matrix (Fin 6 ⊕ Fin 3) (Fin 6 ⊕ Fin 3) R :=
  let half := algebraMap K R a
  let B := sectionBra x
  let F := tripletReadout half (transverseKet 0) B m
  let N := tripletReadout (inl half) (transverseKet (inr 1))
    (fun i => liftCore (B i)) m
  let rotation₀ := tripletRotation false F
  let rotation₁ := tripletRotation true F
  Matrix.fromBlocks ((literalOuterColumn a m).map (aeval x))
    (Matrix.of fun i j => ![outerEntry rotation₀ i, outerEntry rotation₁ i,
      outerEntry (N.map snd) i] j) 0
    (Matrix.of fun i j => ![rotation₀ 1 i, rotation₁ 1 i, snd (N 1 i)] j)

/-- The native triplet minor on the singlet branch factors into the divided
outer determinant, the trace-feature determinant, the root product and
the checked middle factor. -/
theorem sectionTripletMinor_det [Algebra K R] (a : K) (ha : a + a = 1)
    (n : ℕ) (x : Fin 5 → R)
    (hzero : PowerSeries.coeff n (completeSeries (sectionBra x 0) (sectionBra x 1)) = 0) :
    let B := sectionBra x
    (sectionTripletMinor a (n + 2) x).det =
      aeval x (outerDividedDet (R := K) (n + 2)) *
        ((traceFeatures (algebraMap K R a) (B 0) (B 1)).det *
          (x 0 * x 1 * (x 2 * x 3)) * middleFactor (B 0) (B 1) n) := by
  dsimp only
  let B := sectionBra x
  let half := algebraMap K R a
  have hh : half + half = 1 := by rw [← map_add, ha, map_one]
  unfold sectionTripletMinor
  dsimp only
  rw [Matrix.det_fromBlocks_zero₂₁, literalOuterColumn_eq _ ha]
  have hd : ((outerDividedMatrix (n + 2)).map (aeval x)).det =
      aeval x (outerDividedDet (R := K) (n + 2)) :=
    ((aeval x).toRingHom.map_det (outerDividedMatrix (n + 2))).symm
  rw [hd]
  congr 1
  have hb : (pairedBra (B 0) (B 1) : Fin 2 → BondMatrix R) = B := by
    funext i
    fin_cases i <;> rfl
  have hbl : pairedBra (liftCore (B 0)) (liftCore (B 1)) = fun i => liftCore (B i) := by
    funext i
    fin_cases i <;> rfl
  have hmat : (Matrix.of fun i j =>
      ![tripletRotation false (tripletReadout half (transverseKet 0) B (n + 2)) 1 i,
        tripletRotation true (tripletReadout half (transverseKet 0) B (n + 2)) 1 i,
        snd (tripletReadout (inl half) (transverseKet (inr 1))
          (fun i => liftCore (B i)) (n + 2) 1 i)] j) =
        middleTraceBlock half (B 0) (B 1) (n + 2) := by
    ext i j
    fin_cases j
    · exact hb ▸ section_rotation_middle half (B 0) (B 1) (n + 2) false i
    · exact hb ▸ section_rotation_middle half (B 0) (B 1) (n + 2) true i
    · exact hbl ▸ transverse_middle_eq half hh (B 0) (B 1) n i
  rw [hmat]
  exact PeriodicMPSUniformVerticalMiddle.section_middleTraceBlock_det half
    (x 0) (x 1) (x 2) (x 3) (x 3 + (x 2 - x 3) * x 4) n hzero


/-- The first and third bra triplet rows, selected for the singlet minor. -/
private def endpoint (i : Fin 2) : Fin 3 := ![0, 2] i

private def singletRows (B0 B1 : BondMatrix R) (half : R) (m : ℕ) :
    Matrix (Fin 2) (Fin 2) R :=
  Matrix.of fun i j =>
    (tripletFeature half B0 B1 (endpoint i) * (![B0, B1] j) ^ m).trace

/-- The second minor uses two middle triplet entries and the singlet. Its
singlet row is zero on the five section derivatives and on the physical
generators, since the ket commutator has a zero diagonal and the singlet
is invariant under the change of physical frame. -/
def sectionSingletMinor [Algebra K R] (a : K) (m : ℕ) (x : Fin 5 → R) :
    Matrix (Fin 6 ⊕ (Fin 2 ⊕ Fin 1)) (Fin 6 ⊕ (Fin 2 ⊕ Fin 1)) R :=
  let T := sectionTripletMinor a m x
  let B := sectionBra x
  let half := algebraMap K R a
  let middleRows := T.toBlocks₂₂
  let topColumns : Fin 2 ⊕ Fin 1 → Fin 3 :=
    Sum.elim (fun j : Fin 2 => j.castSucc) (fun _ => 2)
  Matrix.fromBlocks T.toBlocks₁₁ (T.toBlocks₁₂.submatrix id topColumns) 0
    (Matrix.fromBlocks
      (middleRows.submatrix endpoint (fun j : Fin 2 => j.castSucc))
      (middleRows.submatrix endpoint (fun _ : Fin 1 => 2)) 0
      (Matrix.of fun _ _ => snd (singletTrace (inl half) (transverseKet (inr 1))
        (fun i => liftCore (B i)) m)))

/-- Exact determinant of the adjacent-pair minor that uses the singlet row. -/
theorem sectionSingletMinor_det [Algebra K R] (a : K) (ha : a + a = 1)
    (n : ℕ) (x : Fin 5 → R) :
    let B := sectionBra x
    let half := algebraMap K R a
    (sectionSingletMinor a (n + 2) x).det =
      aeval x (outerDividedDet (R := K) (n + 2)) *
        ((singletRows (B 0) (B 1) half (n + 2)).det *
          (commutatorDet B * PowerSeries.coeff n (completeSeries (B 0) (B 1)))) := by
  dsimp only
  let B := sectionBra x
  let half := algebraMap K R a
  have hh : half + half = 1 := by rw [← map_add, ha, map_one]
  unfold sectionSingletMinor
  dsimp only
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fin_one]
  have hout : ((sectionTripletMinor a (n + 2) x).toBlocks₁₁).det =
      aeval x (outerDividedDet (R := K) (n + 2)) := by
    change ((literalOuterColumn a (n + 2)).map (aeval x)).det = _
    rw [literalOuterColumn_eq _ ha]
    exact ((aeval x).toRingHom.map_det (outerDividedMatrix (n + 2))).symm
  rw [hout]
  have hb : (pairedBra (B 0) (B 1) : Fin 2 → BondMatrix R) = B := by
    funext i
    fin_cases i <;> rfl
  have hbl : pairedBra (liftCore (B 0)) (liftCore (B 1)) = fun i => liftCore (B i) := by
    funext i
    fin_cases i <;> rfl
  have hmat : ((sectionTripletMinor a (n + 2) x).toBlocks₂₂).submatrix
      endpoint (fun j : Fin 2 => j.castSucc) =
        singletRows (B 0) (B 1) half (n + 2) := by
    ext i j
    fin_cases j
    · exact hb ▸ section_rotation_middle half (B 0) (B 1) (n + 2) false (endpoint i)
    · exact hb ▸ section_rotation_middle half (B 0) (B 1) (n + 2) true (endpoint i)
  rw [hmat]
  have hsinglet := transverse_singlet_eq half hh (B 0) (B 1) n
  rw [hbl, hb] at hsinglet
  rw [Matrix.of_apply, hsinglet]

private theorem section_commutatorDet (r s t u p : R) :
    commutatorDet (pairedBra (sectionB0 r s) (sectionB1 t u p)) =
      -(r - s) ^ 2 * (p - t) * (p - u) := by
  simp [commutatorDet, coreCommutator, pairedBra, sectionB0, sectionB1,
    Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem section_traceFeatures_det (half r s t u p : R) (hh : half + half = 1) :
    (traceFeatures half (sectionB0 r s) (sectionB1 t u p)).det =
      ((r + s) * (t + u) * (r - s) * p +
        (r + s) * (t + u) * s * (t + u) -
        (r + s)^2 * (t + u)^2 + (r + s)^2 * (t*u) + (t + u)^2 * (r*s)) *
        (r - s)^2 * (p - t) * (p - u) := by
  have hhalf : 2 * half = 1 := by rwa [two_mul]
  simp [traceFeatures, tripletFeature, sectionB0, sectionB1, Matrix.det_fin_three,
    Matrix.trace_fin_two, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, pow_two]
  linear_combination
    (((r + s) * (t + u) * (r - s) * p +
        (r + s) * (t + u) * s * (t + u) -
        (r + s)^2 * (t + u)^2 + (r + s)^2 * (t*u) + (t + u)^2 * (r*s)) *
        (r - s)^2 * (p - t) * (p - u)) * hhalf


private theorem affine_ne_zero {F : Type*} [Field F] {a b : F} (ha : a ≠ 0) :
    Polynomial.C a * Polynomial.X + Polynomial.C b ≠ 0 := by
  intro he
  have hc := congrArg (fun g : Polynomial F => g.coeff 1) he
  exact ha (by simpa [Polynomial.coeff_C_mul, Polynomial.coeff_X] using hc)

private theorem pivot_ne_zero {F : Type*} [Field F] (half r s t u : F) (m : ℕ)
    (hh : half + half = 1) (hrs : r - s ≠ 0) (htu : t - u ≠ 0)
    (hα : r + s ≠ 0) (hβ : t + u ≠ 0)
    (hL : r ^ m - s ^ m ≠ 0) (hR : t ^ m - u ^ m ≠ 0) :
    let p := Polynomial.C u + (Polynomial.C t - Polynomial.C u) * Polynomial.X
    (singletRows (sectionB0 (Polynomial.C r) (Polynomial.C s))
      (sectionB1 (Polynomial.C t) (Polynomial.C u) p) (Polynomial.C half) m).det ≠ 0 := by
  let c : F →+* Polynomial F := Polynomial.C
  let q : Polynomial F := Polynomial.X
  let p := c u + (c t - c u) * q
  have ⟨hl, hr⟩ := featurePowers (c half) (c r) (c s) (c t) (c u) q
    (by rw [← map_add, hh, map_one]) (by rw [← map_sub]; exact fun h => htu (Polynomial.C_injective (by simpa using h))) m
  change (singletRows (sectionB0 (c r) (c s)) (sectionB1 (c t) (c u) p) (c half) m).det ≠ 0
  have he :
      (singletRows (sectionB0 (c r) (c s)) (sectionB1 (c t) (c u) p) (c half) m).det =
        c (-(r + s) * (t + u) * (r - s) * (t - u) * (r ^ m - s ^ m) *
          (t ^ m - u ^ m)) * q ^ 2 + c
          ((r ^ m * r^2 + s ^ m * s^2) * (t ^ m * t^2 + u ^ m * u^2) -
            (t ^ m * s^2 + u ^ m * r^2) * (r ^ m * u^2 + s ^ m * t^2)) +
          c (-((r + s) * (r - s) * (t ^ m - u ^ m) * (r ^ m * u^2 + s ^ m * t^2) +
            (t + u) * (t - u) * (r ^ m - s ^ m) * (t ^ m * s^2 + u ^ m * r^2))) * q := by
    rw [Matrix.det_fin_two]
    let B0 := sectionB0 (c r) (c s)
    let B1 := sectionB1 (c t) (c u) p
    change (tripletFeature (c half) B0 B1 0 * B0 ^ m).trace *
      (tripletFeature (c half) B0 B1 2 * B1 ^ m).trace -
      (tripletFeature (c half) B0 B1 0 * B1 ^ m).trace *
      (tripletFeature (c half) B0 B1 2 * B0 ^ m).trace = _
    rw [hl 0, hr 2, hr 0, hl 2]
    simp [upperFeatures, lowerFeatures, p, map_add, map_mul, map_sub, map_pow, map_neg]
    ring
  intro h
  have hc := congrArg (fun g : Polynomial F => g.coeff 2) (he.symm.trans h)
  have hz : -(r + s) * (t + u) * (r - s) * (t - u) * (r ^ m - s ^ m) * (t ^ m - u ^ m) = 0 :=
    by
      change (c _ * Polynomial.X ^ 2 + c _ + c _ * Polynomial.X).coeff 2 = _ at hc
      simpa only [c, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_zero,
        ite_eq_left rfl, ite_eq_right (by decide : (2 : ℕ) ≠ 0),
        ite_eq_right (by decide : (2 : ℕ) ≠ 1), ite_eq_right (by decide : (1 : ℕ) ≠ 2),
        ite_true, mul_zero, mul_one, add_zero] using hc
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (neg_ne_zero.mpr hα) hβ) hrs) htu) hL) hR) hz

private theorem traceFeatures_ne_zero {F : Type*} [Field F] (half r s t u : F)
    (hh : half + half = 1) (hrs : r - s ≠ 0) (htu : t - u ≠ 0)
    (hα : r + s ≠ 0) (hβ : t + u ≠ 0) :
    let p := Polynomial.C u + (Polynomial.C t - Polynomial.C u) * Polynomial.X
    (traceFeatures (Polynomial.C half) (sectionB0 (Polynomial.C r) (Polynomial.C s))
      (sectionB1 (Polynomial.C t) (Polynomial.C u) p)).det ≠ 0 := by
  let c : F →+* Polynomial F := Polynomial.C
  let p := c u + (c t - c u) * Polynomial.X
  have hh' : c half + c half = 1 := by rw [← map_add, hh, map_one]
  have hL : p - c t = c (t-u) * Polynomial.X + c (u-t) := by simp [p, map_sub]; ring
  have hR : p - c u = c (t-u) * Polynomial.X + c 0 := by simp [p, map_sub]
  have ha : c (r - s) ≠ 0 := fun h => hrs (Polynomial.C_injective (by simpa [c] using h))
  change (traceFeatures (c half) (sectionB0 (c r) (c s))
    (sectionB1 (c t) (c u) p)).det ≠ 0
  rw [section_traceFeatures_det _ _ _ _ _ _ hh', hL, hR, ← map_sub]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ ha))
    (affine_ne_zero htu)) (affine_ne_zero htu)
  have hform :
      (c r + c s) * (c t + c u) * c (r - s) * p +
        (c r + c s) * (c t + c u) * c s * (c t + c u) -
        (c r + c s)^2 * (c t + c u)^2 + (c r + c s)^2 * (c t * c u) +
          (c t + c u)^2 * (c r * c s) =
      c ((r+s)*(t+u)*(r-s)*(t-u)) * Polynomial.X +
        c ((r+s)*(t+u)*(r-s)*u + (r+s)*(t+u)*s*(t+u) -
          (r+s)^2*(t+u)^2 + (r+s)^2*(t*u) + (t+u)^2*(r*s)) := by
    simp [p, map_add, map_sub, map_mul, map_pow]
    ring
  exact hform ▸ affine_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hα hβ) hrs) htu)

end Determinants



section Divisor

open PeriodicMPSUniformVerticalPrimeExclusion
open PeriodicMPSUniformVerticalSingletNorm (middlePolynomial section_completeSeries_eq_rootSeries
  aeval_middlePolynomial)
open PeriodicMPSUniformTernaryRemainder (coeff_rootSeries)
open private toSectionPolynomial toSectionPolynomial_X from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalPrimeExclusion

variable {F : Type*} [Field F] [Algebra ℂ F]

/-- The roots of a given pairing, constant in the indeterminate section parameter. -/
def genericSection (φ : Roots →ₐ[ℂ] F) (j : Fin 3) : Fin 5 → Polynomial F :=
  ![Polynomial.C (φ (X (pairing j 0))), Polynomial.C (φ (X (pairing j 1))),
    Polynomial.C (φ (X (pairing j 2))), Polynomial.C (φ (X (pairing j 3))), Polynomial.X]

private theorem generic_outer (φ : Roots →ₐ[ℂ] F) (m : ℕ) (j : Fin 3) :
    aeval (genericSection φ j) (outerDividedDet (R := ℂ) m) =
      (outerPolynomial m j).map φ.toRingHom := by
  let ψ := φ.comp (rename (pairing j))
  have h : (Polynomial.mapAlgHom ψ).comp toSectionPolynomial.toAlgHom =
      aeval (genericSection φ j) := by
    apply algHom_ext
    intro i
    fin_cases i <;> simp [toSectionPolynomial_X, genericSection, ψ, AlgEquiv.coe_toAlgHom]
  rw [← h]
  change (toSectionPolynomial (outerDividedDet (R := ℂ) m)).map ψ.toRingHom = _
  rw [outerPolynomial, Polynomial.map_map]
  rfl

private theorem genericSpectralEval (φ : Roots →ₐ[ℂ] F) (j : Fin 3) :
    let x := genericSection φ j
    aeval (![x 0, x 1, x 2, x 3] : Fin 4 → Polynomial F) =
      (Polynomial.CAlgHom (R := ℂ)).comp (φ.comp (rename (pairing j))) := by
  dsimp only
  apply algHom_ext
  intro i
  fin_cases i <;> simp [genericSection, Polynomial.CAlgHom]

private theorem generic_singlet (φ : Roots →ₐ[ℂ] F) (m : ℕ) (j : Fin 3) :
    PowerSeries.coeff (m - 2)
        (completeSeries (sectionBra (genericSection φ j) 0) (sectionBra (genericSection φ j) 1)) =
      Polynomial.C (φ (singlet m)) := by
  let x := genericSection φ j
  change PowerSeries.coeff (m - 2) (completeSeries (sectionB0 (x 0) (x 1))
    (sectionB1 (x 2) (x 3) (x 3 + (x 2 - x 3) * x 4))) = _
  rw [section_completeSeries_eq_rootSeries, coeff_rootSeries ℂ]
  rw [genericSpectralEval φ j]
  simp [singlet, rename_hsymm]

private theorem generic_middle (φ : Roots →ₐ[ℂ] F) (m : ℕ) (hm : 4 ≤ m) (j : Fin 3) :
    middleFactor (sectionBra (genericSection φ j) 0) (sectionBra (genericSection φ j) 1) (m - 2) =
      Polynomial.C (φ (middle m)) := by
  let x := genericSection φ j
  change middleFactor (sectionB0 (x 0) (x 1))
    (sectionB1 (x 2) (x 3) (x 3 + (x 2 - x 3) * x 4)) (m - 2) = _
  have h := (aeval_middlePolynomial ℂ (x 0) (x 1) (x 2) (x 3)
    (x 3 + (x 2 - x 3) * x 4) (m - 4)).symm
  rw [show m - 4 + 2 = m - 2 by omega] at h
  rw [h, genericSpectralEval φ j]
  simp [middle, middlePolynomial, rename_hsymm]

private theorem good_factors (φ : Roots →ₐ[ℂ] F) (m : ℕ) (j : Fin 3)
    (h : φ (obstruction m j) ≠ 0) :
    let r := φ (X (pairing j 0))
    let s := φ (X (pairing j 1))
    let t := φ (X (pairing j 2))
    let u := φ (X (pairing j 3))
    r + s ≠ 0 ∧ t + u ≠ 0 ∧ r ^ m - s ^ m ≠ 0 ∧ t ^ m - u ^ m ≠ 0 := by
  unfold obstruction at h
  simp only [map_mul, map_add, map_sub, map_pow, ne_eq, mul_eq_zero, not_or] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.2, h.2⟩

/-- Rank failure on the generic paired section forces the exact existing
three-pairing implication. Both rank hypotheses are vanishing statements
for concrete minors of the literal section matrix. Their connection to
the trace-one native chart uses a moving change of physical frame. -/
theorem sectionRankImplication_of_genericSectionMinors
    {m : ℕ} (hm : 3 ≤ m) {f : Roots} (φ : Roots →ₐ[ℂ] F)
    (hker : ∀ g : Roots, φ g = 0 ↔ f ∣ g)
    (htrace : ¬ f ∣ rootSum)
    (htorus : ∀ i : Fin 4, φ (X i) ≠ 0)
    (hrank : ∀ j : Fin 3, ¬ f ∣ obstruction m j →
      (sectionSingletMinor (1 / 2 : ℂ) m (genericSection φ j)).det = 0 ∧
      (sectionTripletMinor (1 / 2 : ℂ) m (genericSection φ j)).det = 0) :
    SectionRankImplication m f := by
  intro j hj
  let r := φ (X (pairing j 0))
  let s := φ (X (pairing j 1))
  let t := φ (X (pairing j 2))
  let u := φ (X (pairing j 3))
  let x := genericSection φ j
  let c : F →+* Polynomial F := Polynomial.C
  let p := c u + (c t - c u) * Polynomial.X
  let half : F := algebraMap ℂ F (1 / 2)
  have hh : half + half = 1 := by simp only [half, ← map_add]; norm_num
  have hC : (algebraMap ℂ (Polynomial F)) (1 / 2) = c half := by
    exact IsScalarTower.algebraMap_apply ℂ F (Polynomial F) _ 
  have ⟨hα, hβ, hL, hR⟩ := good_factors φ m j (fun hz => hj ((hker _).mp hz))
  have hrs : r - s ≠ 0 := sub_ne_zero.mpr (fun h => hL (show r ^ m - s ^ m = 0 by rw [h, sub_self]))
  have htu : t - u ≠ 0 := sub_ne_zero.mpr (fun h => hR (show t ^ m - u ^ m = 0 by rw [h, sub_self]))
  have hc_ne (v : F) (hv : v ≠ 0) : c v ≠ 0 :=
    fun hv' => hv (Polynomial.C_injective (by simpa [c] using hv'))
  by_cases hout : (outerPolynomial m j).map φ.toRingHom = 0
  · left
    apply (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr
    intro i
    apply (hker _).mp
    have h := congrArg (fun g : Polynomial F => g.coeff i) hout
    simpa [Polynomial.coeff_map] using h
  have houter : aeval x (outerDividedDet (R := ℂ) m) ≠ 0 :=
    fun h => hout ((generic_outer φ m j).symm.trans h)
  obtain ⟨hS, hT⟩ := hrank j hj
  have hm' : m - 2 + 2 = m := by omega
  have hdetS := sectionSingletMinor_det (1 / 2 : ℂ) (by norm_num) (m - 2) x
  dsimp only at hdetS
  rw [hm', hS, hC, generic_singlet φ m j] at hdetS
  have hpL : p - c t ≠ 0 := by
    rw [show p - c t = Polynomial.C (t-u) * Polynomial.X + Polynomial.C (u-t) by
      simp [p, c, map_sub]; ring]
    exact affine_ne_zero htu
  have hpR : p - c u ≠ 0 := by
    rw [show p - c u = Polynomial.C (t-u) * Polynomial.X + Polynomial.C 0 by
      simp [p, c, map_sub]]
    exact affine_ne_zero htu
  have hB : PeriodicMPSUniformAntisymmetricTransfer.commutatorDet (sectionBra x) ≠ 0 := by
    change PeriodicMPSUniformAntisymmetricTransfer.commutatorDet
      (pairedBra (sectionB0 (c r) (c s)) (sectionB1 (c t) (c u) p)) ≠ 0
    rw [section_commutatorDet, ← map_sub]
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (hc_ne _ hrs))) hpL) hpR
  have hpivot := pivot_ne_zero half r s t u m hh hrs htu hα hβ hL hR
  have hs : φ (singlet m) = 0 := by
    by_contra hn
    exact (mul_ne_zero houter (mul_ne_zero hpivot (mul_ne_zero hB (hc_ne _ hn)))) hdetS.symm
  have hsdiv := (hker _).mp hs
  have hlarge : 4 ≤ m := by
    by_contra h
    have he : m = 3 := by omega
    exact htrace (by simpa [he, singlet_three] using hsdiv)
  right
  refine ⟨hlarge, hsdiv, (hker _).mp ?_⟩
  have hzero : PowerSeries.coeff (m - 2) (completeSeries (sectionBra x 0) (sectionBra x 1)) = 0 := by
    rw [generic_singlet φ m j, hs, map_zero]
  have hdetT := sectionTripletMinor_det (1 / 2 : ℂ) (by norm_num) (m - 2) x hzero
  dsimp only at hdetT
  rw [hm', hT, hC, generic_middle φ m hlarge j] at hdetT
  have htraceFeatures := traceFeatures_ne_zero half r s t u hh hrs htu hα hβ
  have hprod : x 0 * x 1 * (x 2 * x 3) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (hc_ne r (htorus _)) (hc_ne s (htorus _)))
      (mul_ne_zero (hc_ne t (htorus _)) (hc_ne u (htorus _)))
  by_contra hn
  exact (mul_ne_zero houter (mul_ne_zero (mul_ne_zero htraceFeatures hprod) (hc_ne _ hn))) hdetT.symm


/-- The coordinate ring of the spectral divisor. -/
abbrev DivisorRing (f : Roots) := Roots ⧸ Ideal.span ({f} : Set Roots)

/-- Send the four spectral coordinates to the fraction field of the divisor. -/
def divisorRoots (f : Roots) [IsDomain (DivisorRing f)] :
    Roots →ₐ[ℂ] FractionRing (DivisorRing f) :=
  (IsScalarTower.toAlgHom ℂ (DivisorRing f) (FractionRing (DivisorRing f))).comp
    (Ideal.Quotient.mkₐ ℂ (Ideal.span ({f} : Set Roots)))

private theorem divisorRoots_eq_zero (f : Roots) [IsDomain (DivisorRing f)] (g : Roots) :
    divisorRoots f g = 0 ↔ f ∣ g := by
  change algebraMap (DivisorRing f) (FractionRing (DivisorRing f))
    (Ideal.Quotient.mk (Ideal.span ({f} : Set Roots)) g) = 0 ↔ _
  rw [map_eq_zero_iff _ (IsFractionRing.injective (DivisorRing f) _),
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

/-- Concrete quotient-field form of the vertical-section rank implication.
A moving-frame comparison has to supply the two displayed section minors
from the trace-one chart rank hypothesis. -/
theorem sectionRankImplication_of_divisorMinors {m : ℕ} (hm : 3 ≤ m) {f : Roots}
    [IsDomain (DivisorRing f)] (htrace : ¬ f ∣ rootSum)
    (htorus : ∀ i : Fin 4, ¬ f ∣ (X i : Roots))
    (hrank : ∀ j : Fin 3, ¬ f ∣ obstruction m j →
      (sectionSingletMinor (1 / 2 : ℂ) m (genericSection (divisorRoots f) j)).det = 0 ∧
      (sectionTripletMinor (1 / 2 : ℂ) m (genericSection (divisorRoots f) j)).det = 0) :
    SectionRankImplication m f :=
  sectionRankImplication_of_genericSectionMinors hm (divisorRoots f) (divisorRoots_eq_zero f)
    htrace (fun i h => htorus i ((divisorRoots_eq_zero f _).mp h)) hrank


/-- The already checked three-pairing exclusion applies to the literal
section minors over the fraction field of a noncoordinate divisor. -/
theorem no_divisor_of_genericSectionMinors {m : ℕ} (hm : 3 ≤ m) {f : Roots}
    (hf : Irreducible f) [IsDomain (DivisorRing f)] (htrace : ¬ f ∣ rootSum)
    (htorus : ∀ i : Fin 4, ¬ f ∣ (X i : Roots))
    (hrank : ∀ j : Fin 3, ¬ f ∣ obstruction m j →
      (sectionSingletMinor (1 / 2 : ℂ) m (genericSection (divisorRoots f) j)).det = 0 ∧
      (sectionTripletMinor (1 / 2 : ℂ) m (genericSection (divisorRoots f) j)).det = 0) : False :=
  no_noncoordinate_prime_of_sectionRankImplication hm hf htrace
    (fun i h => htorus i h.dvd) (sectionRankImplication_of_divisorMinors hm htrace htorus hrank)

end Divisor


/-- The row contractions and column changes of a moving frame carry a
right-kernel witness for the native differential to determinant vanishing.
The comparison can take place in a field extension, such as one adjoining
the square root used to put both mixed traces in the same frame. -/
theorem det_eq_zero_of_native_frame {A E ι : Type*} [CommRing A] [Field E]
    [Fintype ι] [DecidableEq ι] (σ : A →+* E) (hσ : Function.Injective σ)
    (M : Matrix ι ι A) (N : Matrix (Fin 10) ι E)
    (L : Matrix ι (Fin 10) E) (C : Matrix ι ι E)
    (hframe : M.map σ = L * N * C)
    (hrank : ∃ v : ι → E, v ≠ 0 ∧ N *ᵥ v = 0) :
    M.det = 0 := by
  obtain ⟨v, hv, hNv⟩ := hrank
  have hLN : (L * N).det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp
    ⟨v, hv, by rw [← Matrix.mulVec_mulVec, hNv, Matrix.mulVec_zero]⟩
  apply hσ
  change σ M.det = σ 0
  rw [map_zero, σ.map_det]
  change (M.map σ).det = 0
  rw [hframe, Matrix.det_mul, hLN, zero_mul]

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformVerticalSectionRank
