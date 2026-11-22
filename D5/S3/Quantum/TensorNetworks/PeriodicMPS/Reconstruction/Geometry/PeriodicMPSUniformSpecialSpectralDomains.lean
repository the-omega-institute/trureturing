/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformSpecialSpectralDomains
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformSpecialSpectralDomains
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: The determinant chart remains integral over each special coefficient divisor. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformSpectralRadicalAlgebra
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformTransferSquareClasses
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformSpecialSpectralBases
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Guarded radical charts on the two special spectral divisors

The coefficient ring is the reduced coordinate ring of each locus with
`c - b²` inverted. The chart then adjoins the independent parameters
`k, U`, inverts both, and adjoins the two radicals in the checked presentation.

The minor transport theorem takes a matrix over this chart and a specialization
of its determinant. Applying it to the literal rank requires identifying the
chart minor with a minor of the complexified adjacent-pair Gram differential
and checking its specialization under the core rescaling and any changes of
rows, tangent directions, or normalization.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformSpecialSpectralDomains

open Polynomial
open scoped TensorProduct
open private radicalTowerEquiv from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformSpectralRadicalAlgebra

noncomputable section

/-- The two special coefficient loci of the trace-one quartic. -/
inductive Divisor
  | zeroRoot
  | repeatedRoot

variable (K : Type*) [Field K] [CharZero K]

def Divisor.locus (d : Divisor) : Set (PeriodicMPSUniformSpecialSpectralBases.Coefficients K) :=
  match d with
  | .zeroRoot => PeriodicMPSUniformSpecialSpectralBases.zeroRootLocus
  | .repeatedRoot => PeriodicMPSUniformSpecialSpectralBases.repeatedRootLocus

variable (d : Divisor)

abbrev coefficientIdeal := MvPolynomial.vanishingIdeal K (d.locus K)

instance coefficientIdeal_isPrime : (coefficientIdeal K d).IsPrime := by
  cases d
  · exact PeriodicMPSUniformSpecialSpectralBases.zeroRoot_vanishingIdeal_isPrime
  · exact PeriodicMPSUniformSpecialSpectralBases.repeatedRoot_vanishingIdeal_isPrime

abbrev DivisorRing := PeriodicMPSUniformSpecialSpectralBases.CoefficientRing K ⧸ coefficientIdeal K d

def coefficientClass : PeriodicMPSUniformSpecialSpectralBases.CoefficientRing K →+* DivisorRing K d :=
  Ideal.Quotient.mk _

def guardClass : DivisorRing K d := coefficientClass K d PeriodicMPSUniformSpecialSpectralBases.guard

theorem guardClass_ne_zero : guardClass K d ≠ 0 := by
  cases d
  · exact PeriodicMPSUniformSpecialSpectralBases.guard_zeroRoot_quotient_ne_zero
  · exact PeriodicMPSUniformSpecialSpectralBases.guard_repeatedRoot_quotient_ne_zero

abbrev GuardedCoefficients := Localization.Away (guardClass K d)
abbrev CoefficientField := FractionRing (DivisorRing K d)

def guardedClass (f : PeriodicMPSUniformSpecialSpectralBases.CoefficientRing K) : GuardedCoefficients K d :=
  algebraMap (DivisorRing K d) (GuardedCoefficients K d) (coefficientClass K d f)

def genericCoefficient (f : PeriodicMPSUniformSpecialSpectralBases.CoefficientRing K) : CoefficientField K d :=
  algebraMap (DivisorRing K d) (CoefficientField K d) (coefficientClass K d f)

private theorem map_guard_ne_zero :
    algebraMap (DivisorRing K d) (CoefficientField K d) (guardClass K d) ≠ 0 := by
  simpa only [map_zero] using
    (IsFractionRing.injective (DivisorRing K d) (CoefficientField K d)).ne
      (guardClass_ne_zero K d)

def guardedCoefficientsToField : GuardedCoefficients K d →+* CoefficientField K d :=
  IsLocalization.Away.lift (guardClass K d) (isUnit_iff_ne_zero.mpr (map_guard_ne_zero K d))

private theorem awayLift_injective {R S : Type*} [CommRing R] [CommRing S]
    {g : R →+* S} (x : R) (hu : IsUnit (g x)) (hg : Function.Injective g) :
    Function.Injective
      (IsLocalization.Away.lift x hu : Localization.Away x →+* S) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers x) _).mpr
  intro a b
  rw [IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq]
  exact ⟨fun h => by
    simpa only [IsLocalization.Away.lift_eq] using
      congrArg (IsLocalization.Away.lift x hu : Localization.Away x →+* S) h,
    fun h => congrArg _ (hg h)⟩

theorem guardedCoefficientsToField_injective :
    Function.Injective (guardedCoefficientsToField K d) :=
  awayLift_injective _ _ (IsFractionRing.injective _ _)

@[simp] theorem guardedCoefficientsToField_guardedClass (f : PeriodicMPSUniformSpecialSpectralBases.CoefficientRing K) :
    guardedCoefficientsToField K d (guardedClass K d f) = genericCoefficient K d f :=
  IsLocalization.Away.lift_eq _ _ _

/-- The inner polynomial variable is `k`, and the outer polynomial variable is `U`. -/
abbrev ChartPolynomials := Polynomial (Polynomial (GuardedCoefficients K d))

def polyU : ChartPolynomials K d := X

def polyK : ChartPolynomials K d := C X

abbrev ChartBase := Localization.Away (polyU K d * polyK K d)
abbrev ChartField := PeriodicMPSUniformTransferRadicals.ChartFunctionField (CoefficientField K d)

private def chartPolynomialMap : ChartPolynomials K d →+* ChartField K d :=
  (algebraMap (Polynomial (RatFunc (CoefficientField K d))) (ChartField K d)).comp
    (Polynomial.mapRingHom <|
      (algebraMap (Polynomial (CoefficientField K d)) (RatFunc (CoefficientField K d))).comp
        (Polynomial.mapRingHom (guardedCoefficientsToField K d)))

private theorem chartPolynomialMap_injective :
    Function.Injective (chartPolynomialMap K d) :=
  (RatFunc.algebraMap_injective _).comp <|
    Polynomial.map_injective _ <| (RatFunc.algebraMap_injective _).comp <|
      Polynomial.map_injective _ (guardedCoefficientsToField_injective K d)

@[simp] private theorem chartPolynomialMap_U :
    chartPolynomialMap K d (polyU K d) = RatFunc.X := by
  simp [chartPolynomialMap, polyU, RatFunc.algebraMap_X]

@[simp] private theorem chartPolynomialMap_k :
    chartPolynomialMap K d (polyK K d) = RatFunc.C (RatFunc.X : RatFunc (CoefficientField K d)) := by
  simp [chartPolynomialMap, polyK, RatFunc.algebraMap_C, RatFunc.algebraMap_X]

@[simp] private theorem chartPolynomialMap_C_C (r : GuardedCoefficients K d) :
    chartPolynomialMap K d (C (C r)) = RatFunc.C (RatFunc.C (guardedCoefficientsToField K d r)) := by
  simp [chartPolynomialMap, RatFunc.algebraMap_C]

private theorem chartPolynomialMap_guard_isUnit :
    IsUnit (chartPolynomialMap K d (polyU K d * polyK K d)) := by
  rw [map_mul, chartPolynomialMap_U, chartPolynomialMap_k]
  exact (isUnit_iff_ne_zero.mpr RatFunc.X_ne_zero).mul
    (isUnit_iff_ne_zero.mpr (by
      simpa only [map_zero] using
        (RatFunc.C_injective (K := RatFunc (CoefficientField K d))).ne RatFunc.X_ne_zero))

def chartBaseToField : ChartBase K d →+* ChartField K d :=
  IsLocalization.Away.lift (polyU K d * polyK K d) (g := chartPolynomialMap K d)
    (chartPolynomialMap_guard_isUnit K d)

theorem chartBaseToField_injective : Function.Injective (chartBaseToField K d) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (polyU K d * polyK K d)) (chartBaseToField K d)).mpr
  intro a b
  simp only [chartBaseToField, IsLocalization.Away.lift_eq]
  refine ⟨fun h => ?_, fun h => congrArg _ (chartPolynomialMap_injective K d h)⟩
  simpa only [chartBaseToField, IsLocalization.Away.lift_eq] using
    congrArg (chartBaseToField K d) h

private def toAway {R : Type*} [CommRing R] (x : R) : R →+* Localization.Away x :=
  algebraMap R (Localization.Away x)

private abbrev polynomialToBase := toAway (polyU K d * polyK K d)

def chartConstant (r : GuardedCoefficients K d) : ChartBase K d :=
  polynomialToBase K d (C (C r))

def chartU : (ChartBase K d)ˣ :=
  (IsLocalization.Away.isUnit_of_dvd (x := polyU K d * polyK K d)
    (S := ChartBase K d) (dvd_mul_right (polyU K d) (polyK K d))).unit

def chartK : (ChartBase K d)ˣ :=
  (IsLocalization.Away.isUnit_of_dvd (x := polyU K d * polyK K d)
    (S := ChartBase K d) (dvd_mul_left (polyK K d) (polyU K d))).unit

private def constantMap : K →+* ChartBase K d := by
  let toPolynomials : GuardedCoefficients K d →+* ChartPolynomials K d :=
    (C (R := Polynomial (GuardedCoefficients K d))).comp (C (R := GuardedCoefficients K d))
  exact (polynomialToBase K d).comp (toPolynomials.comp
    ((algebraMap (DivisorRing K d) (GuardedCoefficients K d)).comp
      ((coefficientClass K d).comp MvPolynomial.C)))

def chartParameters : PeriodicMPSUniformSpectralRadicalAlgebra.Parameters (ChartBase K d) where
  a := chartConstant K d (guardedClass K d (MvPolynomial.X 0))
  b := chartConstant K d (guardedClass K d (MvPolynomial.X 1))
  c := chartConstant K d (guardedClass K d (MvPolynomial.X 2))
  U := chartU K d
  k := chartK K d
  two := Units.map (constantMap K d) (Units.mk0 (2 : K) (by norm_num))
  two_val := by
    change constantMap K d (2 : K) = 2
    exact map_ofNat _ 2

/-- The guarded upper chart, with the finite free basis of the monic tower. -/
abbrev Upstairs := PeriodicMPSUniformSpectralRadicalAlgebra.RadicalAlgebra (chartParameters K d)

/-- The literal determinant-coordinate presentation of the same upper chart. -/
abbrev DeterminantChart := PeriodicMPSUniformSpectralRadicalAlgebra.CoordinateAlgebra (chartParameters K d)

def determinantChartEquiv : DeterminantChart K d ≃ₐ[ChartBase K d] Upstairs K d :=
  PeriodicMPSUniformSpectralRadicalAlgebra.coordinateEquivRadicalAlgebra _

theorem upstairs_finrank : Module.finrank (ChartBase K d) (Upstairs K d) = 4 := by
  have h : (0 : ChartBase K d) ≠ 1 := by
    intro hz
    have he := congrArg (chartBaseToField K d) hz
    rw [map_zero, map_one] at he
    exact zero_ne_one he
  have : Nontrivial (ChartBase K d) := ⟨⟨0, 1, h⟩⟩
  exact PeriodicMPSUniformSpectralRadicalAlgebra.radicalAlgebra_finrank _

def genericA : CoefficientField K d := genericCoefficient K d (MvPolynomial.X 0)
def genericB : CoefficientField K d := genericCoefficient K d (MvPolynomial.X 1)
def genericC : CoefficientField K d := genericCoefficient K d (MvPolynomial.X 2)

theorem generic_guard_ne_zero : genericC K d - genericB K d ^ 2 ≠ 0 := by
  simpa [guardClass, genericC, genericB, genericCoefficient, PeriodicMPSUniformSpecialSpectralBases.guard] using map_guard_ne_zero K d

@[simp] private theorem chartBaseToField_constant (r : GuardedCoefficients K d) :
    chartBaseToField K d (chartConstant K d r) = RatFunc.C (RatFunc.C (guardedCoefficientsToField K d r)) := by
  rw [chartBaseToField, chartConstant, polynomialToBase, toAway, IsLocalization.Away.lift_eq, chartPolynomialMap_C_C]

@[simp] private theorem chartBaseToField_U : chartBaseToField K d ↑(chartU K d) = RatFunc.X := by
  rw [chartBaseToField, chartU, IsUnit.unit_spec, IsLocalization.Away.lift_eq, chartPolynomialMap_U]

@[simp] private theorem chartBaseToField_k :
    chartBaseToField K d ↑(chartK K d) = RatFunc.C (RatFunc.X : RatFunc (CoefficientField K d)) := by
  rw [chartBaseToField, chartK, IsUnit.unit_spec, IsLocalization.Away.lift_eq, chartPolynomialMap_k]

abbrev GenericParameters := (chartParameters K d).map (chartBaseToField K d)

private theorem genericParameters_deltaD :
    (GenericParameters K d).deltaD = PeriodicMPSUniformTransferRadicals.genericDeltaD (genericA K d) (genericB K d) := by
  simp [PeriodicMPSUniformSpectralRadicalAlgebra.Parameters.deltaD, PeriodicMPSUniformSpectralRadicalAlgebra.Parameters.sumD, PeriodicMPSUniformSpectralRadicalAlgebra.Parameters.map, chartParameters,
    PeriodicMPSUniformTransferRadicals.genericDeltaD, PeriodicMPSUniformTransferRadicals.deltaD, PeriodicMPSUniformTransferRadicals.sumD, genericA, genericB]

private theorem genericParameters_deltaS :
    (GenericParameters K d).deltaS = PeriodicMPSUniformTransferRadicals.genericDeltaS (genericB K d) (genericC K d) := by
  simp [PeriodicMPSUniformSpectralRadicalAlgebra.Parameters.deltaS, PeriodicMPSUniformSpectralRadicalAlgebra.Parameters.sumS, PeriodicMPSUniformSpectralRadicalAlgebra.Parameters.map, chartParameters,
    PeriodicMPSUniformTransferRadicals.genericDeltaS, PeriodicMPSUniformTransferRadicals.deltaS, PeriodicMPSUniformTransferRadicals.sumScaledE, genericB, genericC, div_eq_mul_inv,
    inv_pow, Units.val_inv_eq_inv_val]

abbrev GenericUpstairs := PeriodicMPSUniformTransferRadicals.GenericRadicalAlgebra
  (genericA K d) (genericB K d) (genericC K d)

theorem genericUpstairs_isField : IsField (GenericUpstairs K d) := by
  let f : K →+* CoefficientField K d :=
    (algebraMap (DivisorRing K d) (CoefficientField K d)).comp
      ((coefficientClass K d).comp MvPolynomial.C)
  have h₂ : (2 : CoefficientField K d) ≠ 0 := by
    simpa only [map_ofNat, map_zero] using f.injective.ne (two_ne_zero (α := K))
  exact PeriodicMPSUniformTransferRadicals.genericRadicalAlgebra_isField _ _ _ h₂
    (generic_guard_ne_zero K d)

private def genericEquiv :
    PeriodicMPSUniformSpectralRadicalAlgebra.RadicalAlgebra (GenericParameters K d) ≃+*
      GenericUpstairs K d :=
  radicalTowerEquiv _ _ _ (genericParameters_deltaD K d) (genericParameters_deltaS K d)

section GenericPoint

local instance chartFieldAlgebra : Algebra (ChartBase K d) (ChartField K d) :=
  (chartBaseToField K d).toAlgebra

local notation "baseChange" => PeriodicMPSUniformSpectralRadicalAlgebra.radicalBaseChange

/-- Base change followed by the identification with the checked generic field. -/
noncomputable def genericPoint : Upstairs K d →+* GenericUpstairs K d :=
  (genericEquiv K d).toRingHom.comp
    ((baseChange (p := chartParameters K d) (ChartField K d)).toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeRight : Upstairs K d →ₐ[ChartBase K d]
        ChartField K d ⊗[ChartBase K d] Upstairs K d).toRingHom)

theorem genericPoint_injective : Function.Injective (genericPoint K d) := by
  classical
  let B := PeriodicMPSUniformSpectralRadicalAlgebra.radicalBasis (chartParameters K d)
  have h : Function.Injective (fun x : Upstairs K d =>
      (1 : ChartField K d) ⊗ₜ[ChartBase K d] x) := by
    intro x y hxy
    apply B.repr.injective
    ext i
    have hi := congrArg (fun z => (B.baseChange (ChartField K d)).repr z i) hxy
    simp only [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one] at hi
    exact chartBaseToField_injective K d hi
  exact (genericEquiv K d).injective.comp
    ((baseChange (p := chartParameters K d) (ChartField K d)).injective.comp h)

instance upstairs_isDomain : IsDomain (Upstairs K d) := by
  let : IsDomain (GenericUpstairs K d) := (genericUpstairs_isField K d).isDomain
  exact (genericPoint_injective K d).isDomain (genericPoint K d)

/-- The generic point in the determinant-coordinate presentation. -/
noncomputable def determinantGenericPoint : DeterminantChart K d →+* GenericUpstairs K d :=
  (genericPoint K d).comp (determinantChartEquiv K d).toAlgHom.toRingHom

theorem determinantGenericPoint_injective : Function.Injective (determinantGenericPoint K d) :=
  (genericPoint_injective K d).comp (determinantChartEquiv K d).injective

instance determinantChart_isDomain : IsDomain (DeterminantChart K d) := by
  let : IsDomain (GenericUpstairs K d) := (genericUpstairs_isField K d).isDomain
  exact (determinantGenericPoint_injective K d).isDomain (determinantGenericPoint K d)

variable {L : Type*} [CommRing L]

theorem genericPoint_ne_zero_of_eval_ne_zero (eval : Upstairs K d →+* L)
    {f : Upstairs K d} (hf : eval f ≠ 0) : genericPoint K d f ≠ 0 := by
  have hz : f ≠ 0 := fun h => hf (h ▸ map_zero eval)
  simpa only [map_zero] using (genericPoint_injective K d).ne hz

theorem determinantGenericPoint_ne_zero_of_eval_ne_zero (eval : DeterminantChart K d →+* L)
    {f : DeterminantChart K d} (hf : eval f ≠ 0) : determinantGenericPoint K d f ≠ 0 := by
  have hz : f ≠ 0 := fun h => hf (h ▸ map_zero eval)
  simpa only [map_zero] using (determinantGenericPoint_injective K d).ne hz

theorem generic_minor_ne_zero_of_eval_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (eval : DeterminantChart K d →+* L) (M : Matrix ι ι (DeterminantChart K d))
    (hM : (M.map eval).det ≠ 0) : (M.map (determinantGenericPoint K d)).det ≠ 0 := by
  change ((determinantGenericPoint K d).mapMatrix M).det ≠ 0
  rw [← RingHom.map_det]
  apply determinantGenericPoint_ne_zero_of_eval_ne_zero K d eval
  rw [RingHom.map_det]
  exact hM

end GenericPoint

section Evaluation

open PeriodicMPSUniformSpectralRadicalAlgebra (Parameters CoordinateFiber coordinateLift coordinate
  coordinateLift_coordinate)
open PeriodicMPSUniformSpecialSpectralBases (Coefficients guard eval_guard commonCoefficients
  commonCoefficients_spec commonCoefficients_mem_repeatedRootLocus)

variable {L : Type*} [Field L]

/-- Evaluate the reduced coefficient ring at a point of the chosen divisor. -/
def divisorEval (p : Coefficients K) (hp : p ∈ d.locus K) : DivisorRing K d →+* K :=
  Ideal.Quotient.lift _ (MvPolynomial.eval p) fun _ hf =>
    MvPolynomial.mem_vanishingIdeal_iff.mp hf p hp

/-- Evaluation of the coefficient ring extends along any field map on the guard open. -/
def guardedCoefficientEval (f : K →+* L) (p : Coefficients K) (hp : p ∈ d.locus K)
    (hg : p 2 - (p 1)^2 ≠ 0) : GuardedCoefficients K d →+* L :=
  IsLocalization.Away.lift (guardClass K d) (g := f.comp (divisorEval K d p hp))
    (isUnit_iff_ne_zero.mpr (by
      have hh : (divisorEval K d p hp) (guardClass K d) ≠ 0 := by
        change MvPolynomial.eval p guard ≠ 0
        rwa [eval_guard]
      simpa only [RingHom.comp_apply, map_zero] using f.injective.ne hh))

omit [CharZero K] in
@[simp] theorem guardedCoefficientEval_class
    (f : K →+* L) (p : Coefficients K) (hp : p ∈ d.locus K) (hg : p 2 - (p 1)^2 ≠ 0)
    (q : PeriodicMPSUniformSpecialSpectralBases.CoefficientRing K) :
    guardedCoefficientEval K d f p hp hg (guardedClass K d q) = f (MvPolynomial.eval p q) :=
  IsLocalization.Away.lift_eq _ _ _

/-- Evaluate the two independent chart parameters at nonzero values. -/
def chartBaseEval (f : GuardedCoefficients K d →+* L) (U k : Lˣ) : ChartBase K d →+* L :=
  IsLocalization.Away.lift (polyU K d * polyK K d) (g := eval₂RingHom (eval₂RingHom f ↑k) ↑U) (by
    simp [polyU, polyK, map_mul, coe_eval₂RingHom, eval₂_C, eval₂_X])

omit [CharZero K] in
@[simp] theorem chartBaseEval_constant (f : GuardedCoefficients K d →+* L)
    (U k : Lˣ) (r : GuardedCoefficients K d) :
    chartBaseEval K d f U k (chartConstant K d r) = f r := by
  rw [chartBaseEval, chartConstant, polynomialToBase, toAway, IsLocalization.Away.lift_eq]
  simp [coe_eval₂RingHom, eval₂_C]

omit [CharZero K] in
@[simp] theorem chartBaseEval_U (f : GuardedCoefficients K d →+* L) (U k : Lˣ) :
    chartBaseEval K d f U k ↑(chartU K d) = (U : L) := by
  rw [chartBaseEval, chartU, IsUnit.unit_spec, IsLocalization.Away.lift_eq]
  simp [polyU, coe_eval₂RingHom, eval₂_X]

omit [CharZero K] in
@[simp] theorem chartBaseEval_k (f : GuardedCoefficients K d →+* L) (U k : Lˣ) :
    chartBaseEval K d f U k ↑(chartK K d) = (k : L) := by
  rw [chartBaseEval, chartK, IsUnit.unit_spec, IsLocalization.Away.lift_eq]
  simp [polyK, coe_eval₂RingHom, eval₂_C, eval₂_X]

/-- A determinant-coordinate solution above an evaluated base gives a point of the chart. -/
def determinantPoint (f : ChartBase K d →+* L)
    (q : CoordinateFiber ((chartParameters K d).map f)) : DeterminantChart K d →+* L := by
  letI : Algebra (ChartBase K d) L := f.toAlgebra
  exact (coordinateLift q).toRingHom

@[simp] theorem determinantPoint_coordinate (f : ChartBase K d →+* L)
    (q : CoordinateFiber ((chartParameters K d).map f))
    (i : PeriodicMPSUniformSpectralRadicalAlgebra.Determinant) :
    determinantPoint K d f q (coordinate _ i) = (match i with
      | .d => q.d
      | .db => q.db
      | .e => q.e
      | .eb => q.eb) := by
  let : Algebra (ChartBase K d) L := f.toAlgebra
  exact coordinateLift_coordinate q i

theorem commonCoefficients_mem_locus : (commonCoefficients : Coefficients K) ∈ d.locus K := by
  cases d
  · exact commonCoefficients_spec.1
  · exact commonCoefficients_mem_repeatedRootLocus

private theorem commonCoefficients_guard :
    (commonCoefficients : Coefficients K) 2 - (commonCoefficients : Coefficients K) 1 ^ 2 ≠ 0 := by
  norm_num [commonCoefficients]

end Evaluation

section SharedWitness

open PeriodicMPSUniformSpectralRadicalAlgebra (CoordinateFiber Parameters)
open PeriodicMPSUniformSpecialSpectralBases (commonCoefficients rationalWitness_common_loci_and_minor)

/-- The rational coefficient witness has an equal-mixed-trace representative over `ℝ`.
The two factors of the original mixed trace product are `-1` and `-3`. -/
def witnessK : ℝˣ :=
  Units.mk0 (Real.sqrt 3) (Real.sqrt_ne_zero'.mpr (by norm_num))

private theorem witnessK_sq : (witnessK : ℝ)^2 = 3 :=
  Real.sq_sqrt (by norm_num)

/-- Inverse rescaling of the two second cores of the literal rational witness. -/
def balancedWitnessCore (i : Fin 4) : Matrix (Fin 2) (Fin 2) ℝ :=
  (![1, -(witnessK : ℝ), 1, (-(witnessK : ℝ))⁻¹] : Fin 4 → ℝ) i •
    (PeriodicMPSCommonSpectralJets.cores i).map (Rat.castHom ℝ)

theorem balancedWitnessCore_data :
    (balancedWitnessCore 0).det = 1 ∧ (balancedWitnessCore 2).det = 3 ∧
    (balancedWitnessCore 1).det = 0 ∧ (balancedWitnessCore 3).det = -2 ∧
    (balancedWitnessCore 0 * balancedWitnessCore 1).trace = (witnessK : ℝ) ∧
    (balancedWitnessCore 2 * balancedWitnessCore 3).trace = (witnessK : ℝ) := by
  have hk : (witnessK : ℝ) ≠ 0 := Units.ne_zero witnessK
  norm_num [balancedWitnessCore, PeriodicMPSCommonSpectralJets.cores, Matrix.det_smul,
    Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.smul_apply, ← inv_pow, witnessK_sq]
  field_simp [hk]
  norm_num [witnessK_sq]

def witnessBase : ChartBase ℚ d →+* ℝ :=
  chartBaseEval ℚ d
    (guardedCoefficientEval ℚ d (Rat.castHom ℝ) commonCoefficients
      (commonCoefficients_mem_locus ℚ d) (commonCoefficients_guard ℚ))
    (Units.mk0 3 (by norm_num)) witnessK

private def witnessFiber : CoordinateFiber ((chartParameters ℚ d).map (witnessBase d)) where
  d := 1
  db := 3
  e := 0
  eb := -2
  prod_eq := by norm_num [Parameters.map, chartParameters, witnessBase]
  coeff_a := by
    simp [Parameters.map, chartParameters, witnessBase, commonCoefficients, witnessK_sq]
    norm_num
  coeff_b := by norm_num [Parameters.map, chartParameters, witnessBase, commonCoefficients]
  coeff_c := by
    simp [Parameters.map, chartParameters, witnessBase, commonCoefficients, witnessK_sq]
    norm_num

/-- Determinant coordinates of the common point after inverse rescaling of the second cores. -/
def sharedWitnessPoint : DeterminantChart ℚ d →+* ℝ :=
  determinantPoint ℚ d (witnessBase d) (witnessFiber d)

theorem sharedWitness_minor_generic_ne_zero {m : ℕ} (hm : 5 ≤ m)
    (M : Matrix (Fin 9) (Fin 9) (DeterminantChart ℚ d))
    (u : ℝˣ)
    (hM : (M.map (sharedWitnessPoint d)).det =
      (u : ℝ) * ((PeriodicMPSCommonSpectralJets.literalJacobian m).det : ℝ)) :
    (M.map (determinantGenericPoint ℚ d)).det ≠ 0 := by
  apply generic_minor_ne_zero_of_eval_ne_zero ℚ d (sharedWitnessPoint d)
  rw [hM]
  refine mul_ne_zero (Units.ne_zero u) ?_
  exact_mod_cast (rationalWitness_common_loci_and_minor hm).2.2.2

end SharedWitness

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformSpecialSpectralDomains
