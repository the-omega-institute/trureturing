/- Source only: native elaboration and kernel acceptance have not been run. -/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleProductMultiplicity

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleRealization

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeDiscriminantTheta LatticeDualCosetModule LatticeDualCosetTransport LatticeSugawaraCurrents
open FullJacobiCurrentTransport FullJacobiIntertwiner
open FullJacobiTensorModule FullJacobiDirectSum
open ActualCurrentTaylor ActualGroundJointWeights ActualGroundChargedSelection
open ActualWeakModuleSectorCoordinates ActualWeakModuleClassification
open ActualWeakModuleScalarProbes ActualWeakModuleProductMultiplicity

open private currentState_single from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleClassification
open private jointWeightMap from D5.S3.VertexAlgebra.Modules.ActualWeakModuleHom
open private gramMap_injective class_representative class_add class_gram from
  D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta

universe u v
variable {D : LatticeData}
attribute [local instance] Classical.propDecidable

variable (W : Discriminant D → Type u)
variable [∀ c, AddCommGroup (W c)] [∀ c, Module ℂ (W c)]

/-- The original representative-sector realization; W is entirely arbitrary. -/
abbrev RealizationCarrier := ⨁ c : Discriminant D, Carrier D ⊗[ℂ] W c

def realization : FullJacobiLatticeModule D (RealizationCarrier W) :=
  directSumModule (fun c => tensorModule (sectorModule D (representative D c)) (W c))

/-- The literal vacuum inclusion satisfies the original positive and zero currents. -/
private theorem vacuum_mem (c : Discriminant D) (w : W c) :
    let z := DirectSum.lof ℂ _ (fun d => Carrier D ⊗[ℂ] W d) c
      (Finsupp.single 0 (1 : Oscillator D) ⊗ₜ[ℂ] w)
    z ∈ Omega (realization W) ∧ ∀ i : Fin D.rank,
      current (realization W) i 0 z = (representative D c i : ℂ) • z := by
  let z := DirectSum.lof ℂ _ (fun d => Carrier D ⊗[ℂ] W d) c
    (Finsupp.single 0 (1 : Oscillator D) ⊗ₜ[ℂ] w)
  have hc (i : Fin D.rank) (m : ℤ) :
      current (realization W) i m z =
        DirectSum.lof ℂ _ (fun d => Carrier D ⊗[ℂ] W d) c
          (Finsupp.single 0
            (shiftedCurrentPolynomial D (representative D c) 1 i 0 m 1) ⊗ₜ[ℂ] w) := by
    change (mode (directSumModule (fun d => tensorModule
      (sectorModule D (representative D d)) (W d))) (currentState D i) m) z = _
    rw [directSumModule_mode, DirectSum.lmap_lof, tensorModule_mode,
      TensorProduct.map_tmul, LinearMap.id_apply]
    rw [sectorModule_mode, currentState_single, action_current_coefficients]
  refine ⟨?_, ?_⟩
  · apply (mem_Omega _ _).mpr
    intro i r
    rw [hc]
    simp [shiftedCurrentPolynomial, show ¬ ((r : ℤ)+1 < 0) by omega,
      show (r : ℤ)+1 ≠ 0 by omega]
  · intro i
    rw [hc]
    simp [shiftedCurrentPolynomial, z, LatticeGeneratingFieldLocality.bilinear,
      ← TensorProduct.smul_tmul', ← Finsupp.smul_single]

/-- No spectrum hypothesis: this is a vector in the actual nested joint weight. -/
def iota (c : Discriminant D) : W c →ₗ[ℂ] Multiplicity (realization W) c where
  toFun w := ⟨⟨DirectSum.lof ℂ _ (fun d => Carrier D ⊗[ℂ] W d) c
      (Finsupp.single 0 (1 : Oscillator D) ⊗ₜ[ℂ] w), (vacuum_mem W c w).1⟩,
    (mem_jointWeight_iff _ _ _).mpr (vacuum_mem W c w).2⟩
  map_add' x y := by
    apply Subtype.ext; apply Subtype.ext
    simp only [TensorProduct.tmul_add, map_add, Submodule.coe_add]
  map_smul' a x := by
    apply Subtype.ext; apply Subtype.ext
    simp only [TensorProduct.tmul_smul, map_smul, Submodule.coe_smul, RingHom.id_apply]

@[simp] theorem iota_val (c : Discriminant D) (w : W c) :
    (iota W c w).val.val = DirectSum.lof ℂ _ (fun d => Carrier D ⊗[ℂ] W d) c
      (Finsupp.single 0 (1 : Oscillator D) ⊗ₜ[ℂ] w) := rfl

/-- Actual projection, followed by the original charge/monomial coordinate. -/
def kappa (c : Discriminant D) : Multiplicity (realization W) c →ₗ[ℂ] W c where
  toFun z := tensorCoordinates (z.val.val c) (0,0)
  map_add' x y := by
    simp only [Submodule.coe_add, DirectSum.add_apply, map_add, Finsupp.add_apply]
  map_smul' a x := by
    simp only [Submodule.coe_smul, DirectSum.smul_apply, map_smul, Finsupp.smul_apply, RingHom.id_apply]

@[simp] theorem kappa_iota (c : Discriminant D) (w : W c) :
    kappa W c (iota W c w) = w := by
  change tensorCoordinates (((iota W c) w).val.val c) (0,0) = w
  rw [iota_val, DirectSum.lof_apply]
  simp [tensorCoordinates_tmul, ActualWeakModuleScalarProbes.coordinate]

variable (hD : (gramReal D).PosDef)
include hD

/-- Class projection first, Gram injectivity second; no rank or nonzero premise. -/
private theorem representative_weight_iff (c d : Discriminant D) (l : Charge D) :
    representative D d + gramMap D l = representative D c ↔ d = c ∧ l = 0 := by
  constructor
  · intro h
    have hd : d = c := by
      have hh := congrArg (classOf D) h
      simpa only [class_add, class_representative, class_gram, add_zero] using hh
    subst d
    refine ⟨rfl, ?_⟩
    apply gramMap_injective D hD
    have hg : gramMap D l = 0 := add_left_cancel (h.trans (add_zero _).symm)
    simpa only [map_zero] using hg
  · rintro ⟨rfl, rfl⟩
    simp only [map_zero, add_zero]

private def weightComponent (c d : Discriminant D) :
    Multiplicity (realization W) c →ₗ[ℂ]
      jointWeight (tensorModule (sectorModule D (representative D d)) (W d))
        (representative D c) :=
  jointWeightMap (projectionHom
    (fun d => tensorModule (sectorModule D (representative D d)) (W d)) d)
    (representative D c)

/-- Exhaustion proves the complete original vector is the single vacuum tensor. -/
theorem realization_reconstruct (c : Discriminant D) (z : Multiplicity (realization W) c) :
    z.val.val = DirectSum.lof ℂ _ (fun d => Carrier D ⊗[ℂ] W d) c
      (Finsupp.single 0 (1 : Oscillator D) ⊗ₜ[ℂ] kappa W c z) := by
  apply DFinsupp.ext
  intro d
  by_cases hd : d = c
  · subst d
    have hs := joint_single_charge hD (representative D c) (representative D c) 0
      (fun l => by simpa using representative_weight_iff hD c c l)
      (weightComponent W c c z)
    change z.val.val c = _ at hs
    change z.val.val c = (DirectSum.component ℂ _ (fun d => Carrier D ⊗[ℂ] W d) c)
      (DirectSum.lof ℂ _ (fun d => Carrier D ⊗[ℂ] W d) c _)
    rw [DirectSum.component.lof_self]
    exact hs
  · have hz : z.val.val d = 0 := by
      apply (tensorCoordinates (D := D) (W := W d)).injective
      apply Finsupp.ext
      rintro ⟨l,f⟩
      rw [map_zero, Finsupp.zero_apply]
      exact joint_coordinate_exhaustion hD (representative D d) (representative D c)
        (weightComponent W c d z) (l,f)
        (Or.inr (fun h => hd ((representative_weight_iff hD c d l).mp h).1))
    rw [hz]
    simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, hd, Ne.symm hd]

def multiplicityEquiv (c : Discriminant D) :
    Multiplicity (realization W) c ≃ₗ[ℂ] W c where
  toLinearMap := kappa W c
  invFun := iota W c
  left_inv z := by
    apply Subtype.ext; apply Subtype.ext
    exact (realization_reconstruct W hD c z).symm
  right_inv := kappa_iota W c

/-- Upgrade vacuum normalization by actual all-state cyclicity. -/
theorem classification_iota (c : Discriminant D) (w : W c) (v : Carrier D) :
    classified hD (realization W) c (iota W c w) v =
      DirectSum.lof ℂ _ (fun d => Carrier D ⊗[ℂ] W d) c (v ⊗ₜ[ℂ] w) := by
  let f := classified hD (realization W) c (iota W c w)
  let g : Carrier D →ₗ[ℂ] RealizationCarrier W :=
    (DirectSum.lof ℂ _ (fun d => Carrier D ⊗[ℂ] W d) c).comp
      ((TensorProduct.mk ℂ (Carrier D) (W c)).flip w)
  have he : f = g := by
    apply modeHom_ext_of_vacuum D (representative D c)
      (fun a m => mode (realization W) a m)
    · intro a m x
      exact classified_modes hD (realization W) c (iota W c w) a x m
    · intro a m x
      change DirectSum.lof ℂ _ (fun d => Carrier D ⊗[ℂ] W d) c
        ((((action D (representative D c)) a)[[m]]) x ⊗ₜ[ℂ] w) =
        (mode (realization W) a m)
          (DirectSum.lof ℂ _ (fun d => Carrier D ⊗[ℂ] W d) c (x ⊗ₜ[ℂ] w))
      rw [realization, directSumModule_mode, DirectSum.lmap_lof,
        tensorModule_mode, TensorProduct.map_tmul, LinearMap.id_apply]
      rfl
    · exact classification_normalization (realization W) hD c (iota W c w)
  exact LinearMap.congr_fun he v

end D5.S3.VertexAlgebra.Modules.ActualWeakModuleRealization
