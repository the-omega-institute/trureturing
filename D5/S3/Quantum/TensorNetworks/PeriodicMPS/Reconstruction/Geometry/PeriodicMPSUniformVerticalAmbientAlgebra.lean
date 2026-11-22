/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalAmbientAlgebra
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalAmbientAlgebra
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Specialization and generic fields of the ordered chart. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformSpectralRadicalAlgebra
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformTransferSquareClasses
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.Ideal.UFD

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformVerticalAmbient

open Polynomial
open PeriodicMPSUniformSpectralRadicalAlgebra
open PeriodicMPSUniformTransferRadicals
open private radicalTowerEquiv from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformSpectralRadicalAlgebra
open scoped TensorProduct

noncomputable section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

abbrev ParameterPolynomials (R : Type*) [CommRing R] := Polynomial (Polynomial R)
def parameterGuard (R : Type*) [CommRing R] : ParameterPolynomials R := X * C X
abbrev ParameterRing (R : Type*) [CommRing R] := Localization.Away (parameterGuard R)

def parameterConstant : R →+* ParameterRing R :=
  (algebraMap (ParameterPolynomials R) (ParameterRing R)).comp (C.comp C)

def parameterU : (ParameterRing R)ˣ :=
  (IsLocalization.Away.isUnit_of_dvd (parameterGuard R) (dvd_mul_right X (C X))).unit

def parameterK : (ParameterRing R)ˣ :=
  (IsLocalization.Away.isUnit_of_dvd (parameterGuard R) (dvd_mul_left (C X) X)).unit

@[simp] theorem parameterU_val :
    (↑(parameterU (R := R)) : ParameterRing R) = algebraMap (ParameterPolynomials R) _ X :=
  IsUnit.unit_spec _

@[simp] theorem parameterK_val :
    (↑(parameterK (R := R)) : ParameterRing R) = algebraMap (ParameterPolynomials R) _ (C X) :=
  IsUnit.unit_spec _

def parameterEval (f : R →+* S) (U k : Sˣ) : ParameterRing R →+* S :=
  IsLocalization.Away.lift (parameterGuard R)
    (g := eval₂RingHom (eval₂RingHom f ↑k) ↑U) (by
      simp [parameterGuard])

@[simp] theorem parameterEval_constant (f : R →+* S) (U k : Sˣ) (r : R) :
    parameterEval f U k (parameterConstant r) = f r := by
  rw [parameterEval, parameterConstant, RingHom.comp_apply, IsLocalization.Away.lift_eq]
  simp

@[simp] theorem parameterEval_U (f : R →+* S) (U k : Sˣ) :
    parameterEval f U k (↑(parameterU (R := R)) : ParameterRing R) = ↑U := by
  rw [parameterU_val, parameterEval, IsLocalization.Away.lift_eq]
  simp

@[simp] theorem parameterEval_k (f : R →+* S) (U k : Sˣ) :
    parameterEval f U k (↑(parameterK (R := R)) : ParameterRing R) = ↑k := by
  rw [parameterK_val, parameterEval, IsLocalization.Away.lift_eq]
  simp

def chartParameters (two : Rˣ) (h₂ : (two : R) = 2) (a b c : R) : Parameters (ParameterRing R) where
  a := parameterConstant a
  b := parameterConstant b
  c := parameterConstant c
  U := parameterU
  k := parameterK
  two := Units.map (parameterConstant (R := R)).toMonoidHom two
  two_val := by
    change parameterConstant (↑two : R) = 2
    rw [h₂, map_ofNat]

private def parameterPolynomialMap (f : R →+* S) :
    ParameterPolynomials R →+* ParameterPolynomials S :=
  Polynomial.mapRingHom (Polynomial.mapRingHom f)

@[simp] private theorem parameterPolynomialMap_guard (f : R →+* S) :
    parameterPolynomialMap f (parameterGuard R) = parameterGuard S := by
  simp [parameterPolynomialMap, parameterGuard]

def parameterMap (f : R →+* S) : ParameterRing R →+* ParameterRing S :=
  IsLocalization.map (ParameterRing S) (M := Submonoid.powers (parameterGuard R))
    (T := Submonoid.powers (parameterGuard S)) (parameterPolynomialMap f)
    (Submonoid.map_le_iff_le_comap.mp (by
      rw [Submonoid.map_powers, parameterPolynomialMap_guard]))

theorem parameterMap_surjective (f : R →+* S) (hf : Function.Surjective f) :
    Function.Surjective (parameterMap f) := by
  let : IsLocalization ((Submonoid.powers (parameterGuard R)).map (parameterPolynomialMap f))
      (ParameterRing S) := by
    rw [Submonoid.map_powers, parameterPolynomialMap_guard]
    infer_instance
  exact IsLocalization.map_surjective_of_surjective (Submonoid.powers (parameterGuard R))
    (ParameterRing R) (ParameterRing S)
    (Polynomial.map_surjective _ (Polynomial.map_surjective f hf))

theorem parameterMap_ker (f : R →+* S) :
    RingHom.ker (parameterMap f) = (RingHom.ker f).map parameterConstant := by
  rw [parameterMap, IsLocalization.ker_map (S := ParameterRing R)
    (T := Submonoid.powers (parameterGuard S)) _ _
    (by rw [Submonoid.map_powers, parameterPolynomialMap_guard])]
  simp only [parameterPolynomialMap, Polynomial.ker_mapRingHom, Ideal.map_map,
    parameterConstant]

@[simp] theorem parameterMap_constant (f : R →+* S) (r : R) :
    parameterMap f (parameterConstant r) = parameterConstant (f r) := by
  simp [parameterMap, parameterConstant, IsLocalization.map_eq, parameterPolynomialMap]

@[simp] theorem parameterMap_U (f : R →+* S) :
    parameterMap f (↑(parameterU (R := R))) = ↑(parameterU (R := S)) := by
  simp [parameterMap, IsLocalization.map_eq, parameterPolynomialMap]

@[simp] theorem parameterMap_K (f : R →+* S) :
    parameterMap f (↑(parameterK (R := R))) = ↑(parameterK (R := S)) := by
  simp [parameterMap, IsLocalization.map_eq, parameterPolynomialMap]

theorem chartParameters_map (f : R →+* S) (two : Rˣ) (h₂ : (two : R) = 2)
    (a b c : R) :
    (chartParameters two h₂ a b c).map (parameterMap f) =
      chartParameters (two.map f.toMonoidHom) (by simp [h₂, map_ofNat]) (f a) (f b) (f c) := by
  simp only [chartParameters, Parameters.map, Parameters.mk.injEq, Units.ext_iff,
    Units.coe_map, parameterMap_constant]
  simpa [h₂, map_ofNat] using And.intro (parameterMap_U f) (parameterMap_K f)

theorem radicalScalar_injective (p : Parameters R) :
    Function.Injective (algebraMap R (RadicalAlgebra p)) := by
  let B := radicalBasis p
  have h1 : B (0, 0) = 1 := by simp [B]
  intro r s h
  have he := congrArg (fun x => B.repr x (0, 0)) h
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← h1] at he
  simpa using he

/-- The canonical specialization in the fixed four-element radical basis. -/
def specializeRadicals (p : Parameters R) (f : R →+* S) :
    RadicalAlgebra p →+* RadicalAlgebra (p.map f) :=
  letI : Algebra R S := f.toAlgebra
  (radicalBaseChange (p := p) S).toAlgHom.toRingHom.comp
    (Algebra.TensorProduct.includeRight : RadicalAlgebra p →ₐ[R] S ⊗[R] RadicalAlgebra p).toRingHom

@[simp] theorem specializeRadicals_scalar (p : Parameters R) (f : R →+* S) (r : R) :
    specializeRadicals p f (algebraMap R _ r) = algebraMap S _ (f r) := by
  let : Algebra R S := f.toAlgebra
  change radicalBaseChange (p := p) S (Algebra.TensorProduct.includeRight (algebraMap R _ r)) = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R S (S ⊗[R] RadicalAlgebra p),
    AlgEquiv.commutes]
  rfl

@[simp] theorem specializeRadicals_rootD (p : Parameters R) (f : R →+* S) :
    specializeRadicals p f (rootD p) = rootD (p.map f) := by
  let : Algebra R S := f.toAlgebra
  exact radicalBaseChange_rootD (p := p) S

@[simp] theorem specializeRadicals_rootS (p : Parameters R) (f : R →+* S) :
    specializeRadicals p f (rootS p) = rootS (p.map f) := by
  let : Algebra R S := f.toAlgebra
  exact radicalBaseChange_rootS (p := p) S

theorem specializeRadicals_surjective (p : Parameters R) (f : R →+* S)
    (hf : Function.Surjective f) : Function.Surjective (specializeRadicals p f) := by
  classical
  intro z
  let B := radicalBasis p
  let C := radicalBasis (p.map f)
  choose coeff hcoeff using fun i : Fin 2 × Fin 2 => hf (C.repr z i)
  refine ⟨∑ i, coeff i • B i, ?_⟩
  rw [map_sum, ← C.sum_repr z]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ _
  rw [Algebra.smul_def, map_mul, specializeRadicals_scalar, hcoeff, ← Algebra.smul_def]
  simp [B, C]

theorem specializeRadicals_ker (p : Parameters R) (f : R →+* S) :
    RingHom.ker (specializeRadicals p f) =
      (RingHom.ker f).map (algebraMap R (RadicalAlgebra p)) := by
  classical
  let B := radicalBasis p
  let C := radicalBasis (p.map f)
  have hb (i : Fin 2 × Fin 2) : specializeRadicals p f (B i) = C i := by
    rcases i with ⟨i, j⟩
    simp [B, C]
  have hc (z : RadicalAlgebra p) (i : Fin 2 × Fin 2) :
      C.repr (specializeRadicals p f z) i = f (B.repr z i) := by
    have hs (a : R) (j) : specializeRadicals p f (a • B j) = f a • C j := by
      rw [Algebra.smul_def, map_mul, specializeRadicals_scalar, hb, ← Algebra.smul_def]
    have he := congrArg (specializeRadicals p f) (B.sum_repr z)
    rw [map_sum] at he
    simp only [hs] at he
    rw [← he]
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, C.repr_self, Finsupp.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
    simp
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    rw [← B.sum_repr z]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def, mul_comm]
    apply Ideal.mul_mem_left
    apply Ideal.mem_map_of_mem
    rw [RingHom.mem_ker, ← hc, hz, map_zero, Finsupp.zero_apply]
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change specializeRadicals p f (algebraMap R _ r) = 0
    rw [specializeRadicals_scalar, RingHom.mem_ker.mp hr, map_zero]

variable {K : Type*} [Field K]

private def parameterFunctionFieldMap (f : R →+* K) :
    ParameterRing R →+* ChartFunctionField K :=
  parameterEval (RatFunc.C.comp (RatFunc.C.comp f))
    (Units.mk0 RatFunc.X RatFunc.X_ne_zero)
    (Units.mk0 (RatFunc.C RatFunc.X)
      (by simpa only [map_zero] using
        (RatFunc.C : RatFunc K →+* ChartFunctionField K).injective.ne RatFunc.X_ne_zero))

private theorem parameterFunctionFieldMap_injective (f : R →+* K) (hf : Function.Injective f) :
    Function.Injective (parameterFunctionFieldMap f) := by
  let g : ParameterPolynomials R →+* ChartFunctionField K :=
    eval₂RingHom (eval₂RingHom (RatFunc.C.comp (RatFunc.C.comp f))
      (RatFunc.C RatFunc.X)) RatFunc.X
  have he :
      g = (algebraMap (Polynomial (RatFunc K)) (ChartFunctionField K)).comp
        (Polynomial.mapRingHom ((algebraMap (Polynomial K) (RatFunc K)).comp
          (Polynomial.mapRingHom f))) := by
    apply Polynomial.ringHom_ext
    · intro x
      let h := (algebraMap (Polynomial (RatFunc K)) (ChartFunctionField K)).comp
        (Polynomial.mapRingHom ((algebraMap (Polynomial K) (RatFunc K)).comp
          (Polynomial.mapRingHom f)))
      change g (C x) = h (C x)
      have hc : g.comp C = h.comp C := by
        apply Polynomial.ringHom_ext <;>
          simp [g, h, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
      exact RingHom.congr_fun hc x
    · simp [g, RatFunc.algebraMap_X]
  have hg : Function.Injective g := by
    rw [he]
    exact (IsFractionRing.injective (Polynomial (RatFunc K)) _).comp
      (Polynomial.map_injective _ ((IsFractionRing.injective (Polynomial K) _).comp
        (Polynomial.map_injective _ hf)))
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (parameterGuard R)) (parameterFunctionFieldMap f)).mpr
  intro a b
  simp only [parameterFunctionFieldMap, parameterEval, IsLocalization.Away.lift_eq]
  refine ⟨fun h => ?_, fun h => congrArg _ (hg h)⟩
  simpa only [parameterFunctionFieldMap, parameterEval, IsLocalization.Away.lift_eq] using
    congrArg (parameterFunctionFieldMap f) h

/-- Both quadratic adjunctions stay irreducible over the rational-function
field with coefficients in the ordered-root residue field. -/
theorem genericChart_isField (two : Rˣ) (h₂ : (two : R) = 2) (a b c : R)
    (f : R →+* K) (h₂K : (2 : K) ≠ 0) (hc : f c - (f b)^2 ≠ 0) :
    IsField (RadicalAlgebra ((chartParameters two h₂ a b c).map
      (parameterFunctionFieldMap f))) := by
  let p := chartParameters two h₂ a b c
  let q := p.map (parameterFunctionFieldMap f)
  have hd : q.deltaD = genericDeltaD (f a) (f b) := by
    simp [-parameterU_val, -parameterK_val, q, p, chartParameters, parameterFunctionFieldMap, Parameters.deltaD,
      Parameters.sumD, Parameters.map, genericDeltaD, deltaD, sumD]
  have hs : q.deltaS = genericDeltaS (f b) (f c) := by
    simp [-parameterU_val, -parameterK_val, q, p, chartParameters, parameterFunctionFieldMap, Parameters.deltaS,
      Parameters.sumS, Parameters.map, genericDeltaS, deltaS, sumScaledE, div_eq_mul_inv,
      inv_pow, Units.val_inv_eq_inv_val]
  exact (radicalTowerEquiv q _ _ hd hs).isField
    (genericRadicalAlgebra_isField (f a) (f b) (f c) h₂K hc)

/-- Finite freeness injects the entire determinant algebra into the generic
degree-four field, including the divisors on which a radical vanishes. -/
theorem chart_isDomain (two : Rˣ) (h₂ : (two : R) = 2) (a b c : R)
    (f : R →+* K) (hf : Function.Injective f) (h₂K : (2 : K) ≠ 0)
    (hc : f c - (f b)^2 ≠ 0) :
    IsDomain (RadicalAlgebra (chartParameters two h₂ a b c)) := by
  let p := chartParameters two h₂ a b c
  let F := ChartFunctionField K
  let : Algebra (ParameterRing R) F := (parameterFunctionFieldMap f).toAlgebra
  let B := radicalBasis p
  let : IsDomain (RadicalAlgebra (p.map (algebraMap (ParameterRing R) F))) :=
    (genericChart_isField two h₂ a b c f h₂K hc).isDomain
  let g : RadicalAlgebra p →+* _ := (radicalBaseChange (p := p) F).toAlgHom.toRingHom.comp
    (Algebra.TensorProduct.includeRight : RadicalAlgebra p →ₐ[ParameterRing R]
      F ⊗[ParameterRing R] RadicalAlgebra p).toRingHom
  suffices hg : Function.Injective g from hg.isDomain g
  change Function.Injective (fun z => radicalBaseChange (p := p) F (1 ⊗ₜ z))
  intro x y hxy
  apply B.repr.injective
  ext i
  have hi := congrArg (fun z => (B.baseChange F).repr z i)
    ((radicalBaseChange (p := p) F).injective hxy)
  simp only [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one] at hi
  exact parameterFunctionFieldMap_injective f hf hi

end
end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformVerticalAmbient
