/- GID: D5/S3/HomologicalAlgebra/Solid/Measures
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/Measures
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.DiscreteInt
import D5.S3.HomologicalAlgebra.Solid.DerivedLocalReflection

/-!
The canonical measure map from the protected P to the countable product of
discrete integers. This is the concrete map in Rodriguez Camargo, Notes on
Solid Geometry, Lemmas 3.3.3--3.3.4. The proofs here are new, Apache-2.0.
No realization or total-derived existence is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightProfinite OnePoint MonoidalCategory MonoidalClosed
open scoped BigOperators

namespace LightCondensed.Solid
open IntProof

/-- The discrete free-Hom equivalence, with its actual additive structure. -/
def freeHomIntAddEquiv (S : LightProfinite) :
    ((free ℤ).obj S.toCondensed ⟶ Zdisc) ≃+ LocallyConstant S ℤ where
  __ := freeHomDiscreteEquiv ℤ S (ModuleCat.of ℤ ℤ)
  map_add' f g := by
    ext s
    have h := freeHomDiscreteEquiv_sub_apply ℤ S (ModuleCat.of ℤ ℤ) (f + g) g s
    simpa using eq_add_of_sub_eq (by simpa using h.symm)

/-- The characteristic function of the n-th finite point of the convergent sequence. -/
def measureCharacteristic (n : ℕ) : LocallyConstant ℕ∪{∞} ℤ :=
  (truncIndex (n + 1)).map
    (fun i => if i = Option.some (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) then 1 else 0)

@[simp] theorem measureCharacteristic_infty (n : ℕ) :
    measureCharacteristic n ∞ = 0 := by
  simp [measureCharacteristic, LocallyConstant.map, truncIndex, truncIndexFun]

@[simp] theorem measureCharacteristic_nat (n m : ℕ) :
    measureCharacteristic n (m : ℕ∪{∞}) = if m = n then 1 else 0 := by
  by_cases hm : m < n + 1
  · simp [measureCharacteristic, LocallyConstant.map, truncIndex, truncIndexFun, hm,
      Fin.ext_iff]
  · have hmn : m ≠ n := by omega
    simp [measureCharacteristic, LocallyConstant.map, truncIndex, truncIndexFun, hm, hmn]

/-- Evaluation of a measure at one coordinate, before imposing the infinity relation. -/
def measureNumeratorCoordinate (n : ℕ) :
    (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ Zdisc :=
  (freeHomIntAddEquiv (ℕ∪{∞})).symm (measureCharacteristic n)

theorem measureNumeratorCoordinate_relation (n : ℕ) :
    P_map ≫ measureNumeratorCoordinate n = 0 := by
  apply (freeHomDiscreteEquiv ℤ (LightProfinite.of PUnit.{1}) (ModuleCat.of ℤ ℤ)).injective
  ext u
  rw [P_map]
  change freeHomDiscreteEquiv ℤ (LightProfinite.of PUnit.{1}) (ModuleCat.of ℤ ℤ)
    ((free ℤ).map (lightProfiniteToLightCondSet.map ι) ≫ measureNumeratorCoordinate n) u = _
  rw [freeHomDiscreteEquiv_map]
  have hcoord : freeHomDiscreteEquiv ℤ (ℕ∪{∞}) (ModuleCat.of ℤ ℤ)
      (measureNumeratorCoordinate n) = measureCharacteristic n :=
    (freeHomIntAddEquiv (ℕ∪{∞})).apply_symm_apply _
  rw [hcoord]
  change measureCharacteristic n ∞ = _
  rw [measureCharacteristic_infty, freeHomDiscreteEquiv_zero_apply]

/-- The actual n-th coordinate on the exact protected cokernel P. -/
def measureCoordinate (n : ℕ) : P ⟶ Zdisc :=
  P_homMk Zdisc (measureNumeratorCoordinate n) (measureNumeratorCoordinate_relation n)

@[reassoc (attr := simp)] theorem P_proj_measureCoordinate (n : ℕ) :
    P_proj ≫ measureCoordinate n = measureNumeratorCoordinate n := by
  simp [measureCoordinate, P_homMk, P_proj]

/-- Countable integer measures, with the product in light condensed abelian groups. -/
def integerMeasures : LightCondAb := ∏ᶜ (fun _ : ℕ => Zdisc)

theorem integerMeasures_solid : isSolid integerMeasures :=
  isSolid.prop_pi (fun _ : ℕ => Zdisc) (fun _ => isSolid_int)

/-- The canonical map sends the n-th generator to the n-th coordinate vector. -/
def PToIntegerMeasures : P ⟶ integerMeasures := Pi.lift measureCoordinate

@[reassoc (attr := simp)] theorem PToIntegerMeasures_coordinate (n : ℕ) :
    PToIntegerMeasures ≫ Pi.π (fun _ : ℕ => Zdisc) n = measureCoordinate n := by
  simp [PToIntegerMeasures]

/-- Actual countable measures concentrated in degree zero are derived-local. -/
def integerMeasuresDerivedLocal : solidDerivedLocal.FullSubcategory :=
  ⟨(DerivedCategory.singleFunctor LightCondAb 0).obj integerMeasures, by
    apply (isIso_solidDerivedEndomorphism_Q_iff _).2
    intro n
    by_cases hn : n = 0
    · subst n
      exact isSolid.prop_of_iso
        (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 integerMeasures).symm
        integerMeasures_solid
    · exact isSolid.prop_of_isZero
        (HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0 integerMeasures n hn)⟩

/-- A genuine comparison in the full local derived category. Its invertibility
is a remaining measure computation, not part of this definition. -/
def localPToIntegerMeasures :
    solidDerivedLocalReflection.obj ((DerivedCategory.singleFunctor LightCondAb 0).obj P) ⟶
      integerMeasuresDerivedLocal := by
  exact solidDerivedLocalReflectionAdjunction.homEquiv _ _ |>.symm
    ((DerivedCategory.singleFunctor LightCondAb 0).map PToIntegerMeasures)

end LightCondensed.Solid
