/- Source-only candidate; no elaboration or kernel acceptance is claimed.
The full VOA/CFT/anomaly/fusion/string/AdS goal remains active and incomplete.
Attribution: the original discriminant/quadratic and faithful AddChar supplier;
the rational Hahn skew supplier; the original full weak classification/Hom,
finite inclusion generation, dependent product multiplicities and productHom.
No unit, hexagon, rigidity or analytic functional calculus is asserted here. -/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleBraiding
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleProductNaturality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleBalancing

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeDiscriminantTheta LatticeDualCosetModule LatticeDualCosetTransport
open FullJacobiCurrentTransport FullJacobiIntertwiner FullJacobiTensorModule FullJacobiDirectSum
open ActualWeakModuleSectorCoordinates ActualWeakModuleClassification
open ActualWeakModuleIntertwinerExtraction (inclusionLinear inclusion_natural induction_on_inclusions)
open ActualWeakModuleUniversalField (P PairSector targetModule tag tag_apply)
open ActualWeakModuleProductMultiplicity
open ActualWeakModuleProductNaturality (productHom inputMap_elementary)
open ActualWeakModuleHom (recordEquiv restrict)
open private shift_pair from D5.S3.VertexAlgebra.Sectors.LatticeCosetCanonicalLaws
open private pairRaw_symm from D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta

universe u v
variable {D : LatticeData}
attribute [local instance] Classical.propDecidable

/-- The existing faithful character, applied to the existing Q/Z half norm. -/
def thetaScalar (c : Discriminant D) : ℂ :=
  LatticeDiscriminantTheta.phase (quadraticClass D c)

/-- This uses the actual quotient phase, even when its representative is not zero. -/
theorem thetaScalar_ne_zero (c : Discriminant D) : thetaScalar c ≠ 0 := by
  change LatticeDiscriminantTheta.phase
    ((pairRaw D (representative D c) (representative D c) / 2 : ℚ) : QmodZ) ≠ 0
  rw [phase_mk]
  exact Complex.exp_ne_zero _

/-- Zero in the quotient is used; no equality beta_0 = 0 is asserted. -/
theorem quadraticClass_zero (hD : (gramReal D).PosDef) :
    quadraticClass D 0 = 0 := by
  have h := (discriminant_quadratic D hD).2.1 (0 : Discriminant D) (0 : ℤ)
  simpa only [zero_smul, zero_pow (by omega), zero_smul] using h

/-- In particular a nonzero representative beta_0 = G n_0 contributes unit phase. -/
theorem thetaScalar_zero (hD : (gramReal D).PosDef) :
    thetaScalar (0 : Discriminant D) = 1 := by
  unfold thetaScalar
  rw [quadraticClass_zero hD]
  exact LatticeDiscriminantTheta.phase.map_zero_eq_one

/-- Identification with the LITERAL two braiding coefficients, not an inverse.
The skew shift uses the original rational inverse Gram and both representatives. -/
theorem double_phase (c d : Discriminant D) :
    ActualWeakModuleBraiding.phase c d * ActualWeakModuleBraiding.phase d c =
      LatticeDiscriminantTheta.phase (LatticeDiscriminantTheta.pairing D c d) := by
  rw [show ActualWeakModuleBraiding.phase d c = ActualWeakModuleBraiding.phase c d by
    exact LatticeCosetRationalSkew.Omega_symm D (1 : Matrix _ _ ℤ) _ _]
  change Complex.exp _ * Complex.exp _ =
    LatticeDiscriminantTheta.phase (pairRaw D (representative D c) (representative D d) : QmodZ)
  rw [← Complex.exp_add, phase_mk]
  simp only [shift_pair, Matrix.one_mulVec,
    pairRaw_symm D (representative D d) (representative D c)]
  congr 1
  ring

/-- Quadratic refinement is CONSUMED from the existing original even lattice. -/
theorem thetaScalar_add (hD : (gramReal D).PosDef) (c d : Discriminant D) :
    thetaScalar (c+d) =
      (ActualWeakModuleBraiding.phase c d * ActualWeakModuleBraiding.phase d c) *
        (thetaScalar c * thetaScalar d) := by
  unfold thetaScalar
  rw [(discriminant_quadratic D hD).1 c d,
    LatticeDiscriminantTheta.phase.map_add_eq_mul,
    LatticeDiscriminantTheta.phase.map_add_eq_mul, double_phase]
  ring

section Original
variable {X : Type u} [AddCommGroup X] [Module ℂ X]
variable (J : FullJacobiLatticeModule D X)

/-- Scalar multiplication on each ACTUAL algebraic sector tensor. -/
def modelScale (s : Discriminant D → ℂ) : Model J →ₗ[ℂ] Model J :=
  DirectSum.lmap (fun c => s c • (LinearMap.id : Sector J c →ₗ[ℂ] Sector J c))

/-- Every original state and signed mode, on arbitrary sector tensors. -/
theorem modelScale_modes (s : Discriminant D → ℂ) (a : Carrier D) (m : ℤ)
    (x : Model J) :
    modelScale J s (mode (canonicalModule J) a m x) =
      mode (canonicalModule J) a m (modelScale J s x) := by
  have h : (modelScale J s).comp (mode (canonicalModule J) a m) =
      (mode (canonicalModule J) a m).comp (modelScale J s) := by
    apply DirectSum.linearMap_ext
    intro c
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, modelScale, canonicalModule,
      directSumModule_mode, DirectSum.lmap_lof, LinearMap.smul_apply,
      LinearMap.id_apply, map_smul]
  exact LinearMap.congr_fun h x

/-- Both reciprocal cancellations below use this finite direct-sum calculation. -/
private theorem modelScale_cancel (s t : Discriminant D → ℂ)
    (h : ∀ c, t c * s c = 1) (x : Model J) :
    modelScale J t (modelScale J s x) = x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | of c z =>
    simp only [DirectSum.lof_eq_of, modelScale, DirectSum.lmap_lof,
      LinearMap.smul_apply, LinearMap.id_apply, map_smul, smul_smul, h c, one_smul]

/-- Correct conjugation: E : Model J -> X, hence E . scale . E.symm. -/
def conjugateScale (hD : (gramReal D).PosDef) (s : Discriminant D → ℂ) : X →ₗ[ℂ] X :=
  (classificationEquiv J hD).toLinearMap.comp
    ((modelScale J s).comp (classificationEquiv J hD).symm.toLinearMap)

/-- The full original omega is included among these original states. -/
theorem conjugateScale_modes (hD : (gramReal D).PosDef) (s : Discriminant D → ℂ)
    (a : Carrier D) (m : ℤ) (x : X) :
    conjugateScale J hD s (mode J a m x) =
      mode J a m (conjugateScale J hD s x) := by
  change classificationEquiv J hD
    (modelScale J s ((classificationEquiv J hD).symm (mode J a m x))) =
      mode J a m (classificationEquiv J hD
        (modelScale J s ((classificationEquiv J hD).symm x)))
  rw [classification_inverse, modelScale_modes, classification]

private theorem conjugateScale_cancel (hD : (gramReal D).PosDef)
    (s t : Discriminant D → ℂ) (h : ∀ c, t c * s c = 1) (x : X) :
    conjugateScale J hD t (conjugateScale J hD s x) = x := by
  change classificationEquiv J hD (modelScale J t
    ((classificationEquiv J hD).symm (classificationEquiv J hD
      (modelScale J s ((classificationEquiv J hD).symm x))))) = x
  rw [LinearEquiv.symm_apply_apply, modelScale_cancel J s t h,
    LinearEquiv.apply_symm_apply]

/-- The actual twist is a full ModuleIso on the ORIGINAL arbitrary weak module.
The inverse is constructed with reciprocal nonzero phases, in both directions. -/
def theta (hD : (gramReal D).PosDef) : ModuleIso J J where
  linearEquiv :=
    { toLinearMap := conjugateScale J hD (thetaScalar (D := D))
      invFun := conjugateScale J hD (fun c => (thetaScalar (D := D) c)⁻¹)
      left_inv := conjugateScale_cancel J hD _ _
        (fun c => inv_mul_cancel₀ (thetaScalar_ne_zero c))
      right_inv := conjugateScale_cancel J hD _ _
        (fun c => mul_inv_cancel₀ (thetaScalar_ne_zero c)) }
  intertwines := conjugateScale_modes J hD _

/-- Actual sector inclusions at arbitrary carrier vectors, without a ground-only
or basis-only restriction. This computes the defined conjugation. -/
theorem theta_classified (hD : (gramReal D).PosDef) (c : Discriminant D)
    (v : Carrier D) (w : Multiplicity J c) :
    (theta J hD).linearEquiv
      (classificationEquiv J hD (DirectSum.lof ℂ _ (Sector J) c (v ⊗ₜ[ℂ] w))) =
      thetaScalar c •
        classificationEquiv J hD (DirectSum.lof ℂ _ (Sector J) c (v ⊗ₜ[ℂ] w)) := by
  change classificationEquiv J hD (modelScale J _
    ((classificationEquiv J hD).symm (classificationEquiv J hD _))) = _
  rw [LinearEquiv.symm_apply_apply]
  simp only [modelScale, DirectSum.lmap_lof, LinearMap.smul_apply,
    LinearMap.id_apply, map_smul]

/-- Restriction is computed in the actual nested Omega/jointWeight subtype. -/
theorem restrict_theta (hD : (gramReal D).PosDef) (c : Discriminant D)
    (w : Multiplicity J c) :
    restrict (theta J hD).hom c w = thetaScalar c • w := by
  apply Subtype.ext
  apply Subtype.ext
  change (theta J hD).linearEquiv (w.val.val) = thetaScalar c • w.val.val
  rw [← classification_normalization J hD c w, theta_classified,
    classification_normalization]

end Original

section Naturality
variable {X : Type u} {Y : Type v}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable {J : FullJacobiLatticeModule D X} {K : FullJacobiLatticeModule D Y}

/-- Equality of full original ModuleHoms, for independent source/target universes.
Naturality is proved on inclusions by the supplied arbitrary-Hom theorem, then
on every vector by actual finite direct-sum/tensor generation. -/
theorem theta_natural (hD : (gramReal D).PosDef) (f : ModuleHom J K) :
    (theta K hD).hom.comp f = f.comp (theta J hD).hom := by
  apply (recordEquiv J K).injective
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  change (theta K hD).linearEquiv (f.linearMap x) =
    f.linearMap ((theta J hD).linearEquiv x)
  apply induction_on_inclusions hD J x
    (fun x => (theta K hD).linearEquiv (f.linearMap x) =
      f.linearMap ((theta J hD).linearEquiv x))
  · simp
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro c w v
    rw [inclusion_natural]
    change (theta K hD).linearEquiv
      (classificationEquiv K hD (DirectSum.lof ℂ _ _ c (_ ⊗ₜ[ℂ] _))) =
      f.linearMap ((theta J hD).linearEquiv
        (classificationEquiv J hD (DirectSum.lof ℂ _ _ c (_ ⊗ₜ[ℂ] _))))
    rw [theta_classified, theta_classified, map_smul]
    congr 1
    exact (inclusion_natural hD f c w v).symm

end Naturality

section Product
variable {X : Type u} {Y : Type v}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
variable (hD : (gramReal D).PosDef)

/-- Finite dependent-fiber readback of an ARBITRARY classified product inclusion.
mu has direction Multiplicity(P,e)->FiberSum(e); nu has the inverse direction.
The carry transport and all its original reciprocal cocycle factors remain. -/
theorem classification_product_fiber (e : Discriminant D)
    (w : Multiplicity (targetModule A B) e) (v : Carrier D) :
    classificationEquiv (targetModule A B) hD
      (DirectSum.lof ℂ _ _ e (v ⊗ₜ[ℂ] w)) =
      DirectSum.toModule ℂ _ _ (fun i : Fiber (D := D) e =>
        (DirectSum.lof ℂ _ (PairSector A B) i.val).comp
          ((TensorProduct.mk ℂ (Carrier D) (PairMultiplicity A B i.val))
            (transportInverse D (representative D e) (LatticeChargedQuotientScalar.carry D hD i.val.1 i.val.2) v)))
        (mu A B hD e w) := by
  have hf (z : FiberSum A B e) :
      classificationEquiv (targetModule A B) hD
        (DirectSum.lof ℂ _ _ e (v ⊗ₜ[ℂ] nu A B hD e z)) =
      DirectSum.toModule ℂ _ _ (fun i : Fiber (D := D) e =>
        (DirectSum.lof ℂ _ (PairSector A B) i.val).comp
          ((TensorProduct.mk ℂ (Carrier D) (PairMultiplicity A B i.val))
            (transportInverse D (representative D e)
              (LatticeChargedQuotientScalar.carry D hD i.val.1 i.val.2) v))) z := by
    induction z using DirectSum.induction_on with
    | zero => simp
    | add z z' hz hz' =>
      simpa only [map_add, TensorProduct.tmul_add] using congrArg₂ (· + ·) hz hz'
    | of i z =>
      rw [← DirectSum.lof_eq_of, nu_lof, DirectSum.toModule_lof]
      rcases i with ⟨⟨c,d⟩,hi⟩
      dsimp at hi
      subst e
      change classificationEquiv (targetModule A B) hD
        (DirectSum.lof ℂ _ _ (c+d) (v ⊗ₜ[ℂ] j A B hD c d z)) = _
      exact classification_j A B hD c d z v
  calc
    _ = classificationEquiv (targetModule A B) hD
        (DirectSum.lof ℂ _ _ e (v ⊗ₜ[ℂ] nu A B hD e (mu A B hD e w))) := by
      rw [nu_mu]
    _ = _ := hf (mu A B hD e w)

/-- The theta(P) tag formula is DERIVED from the original classification inverse,
the dependent mu/nu readback and jAt, with both carry transports cancelled. -/
theorem theta_product_tag (c d : Discriminant D)
    (x : Multiplicity A c) (y : Multiplicity B d) (v : Carrier D) :
    (theta (targetModule A B) hD).linearEquiv (tag A B c d x y v) =
      thetaScalar (c+d) • tag A B c d x y v := by
  let i : Fiber (D := D) (c+d) := ⟨(c,d),rfl⟩
  let w : PairMultiplicity A B (c,d) := x ⊗ₜ[ℂ] y
  have hj : j A B hD c d w = jAt A B hD (c+d) i w := rfl
  have hf := classification_product_fiber A B hD (c+d)
    (j A B hD c d w)
    (transport D (representative D (c+d)) (LatticeChargedQuotientScalar.carry D hD c d) v)
  rw [hj, mu_jAt, DirectSum.toModule_lof] at hf
  change classificationEquiv (targetModule A B) hD
    (DirectSum.lof ℂ _ _ (c+d)
      (transport D (representative D (c+d)) (LatticeChargedQuotientScalar.carry D hD c d) v
        ⊗ₜ[ℂ] j A B hD c d w)) = _ at hf
  have hc := (transportLinearEquiv D (representative D (c+d))
    (LatticeChargedQuotientScalar.carry D hD c d)).symm_apply_apply v
  change transportInverse D (representative D (c+d))
    (LatticeChargedQuotientScalar.carry D hD c d)
    (transport D (representative D (c+d)) (LatticeChargedQuotientScalar.carry D hD c d) v) = v at hc
  change classificationEquiv (targetModule A B) hD
    (DirectSum.lof ℂ _ _ (c+d)
      (transport D (representative D (c+d)) (LatticeChargedQuotientScalar.carry D hD c d) v
        ⊗ₜ[ℂ] j A B hD c d w)) =
      DirectSum.lof ℂ _ (PairSector A B) (c,d)
        (transportInverse D (representative D (c+d))
          (LatticeChargedQuotientScalar.carry D hD c d)
          (transport D (representative D (c+d))
            (LatticeChargedQuotientScalar.carry D hD c d) v) ⊗ₜ[ℂ] w) at hf
  rw [hc] at hf
  change classificationEquiv (targetModule A B) hD
    (modelScale (targetModule A B) _
      ((classificationEquiv (targetModule A B) hD).symm
        (DirectSum.lof ℂ _ (PairSector A B) (c,d) (v ⊗ₜ[ℂ] w)))) = _
  rw [classification_inverse_pair]
  simp only [modelScale, DirectSum.lmap_lof, LinearMap.smul_apply,
    LinearMap.id_apply, map_smul]
  exact congrArg (fun z : P A B => thetaScalar (c+d) • z) hf

/-- Literal balancing in the ORIGINAL full ModuleHom record, on the dependent
product targetModule/P. The opposite braid contributes its own forward phase. -/
theorem balancing :
    (theta (targetModule A B) hD).hom =
      (ActualWeakModuleBraiding.braidIso B A).hom.comp
        ((ActualWeakModuleBraiding.braidIso A B).hom.comp
          (productHom hD (theta A hD).hom (theta B hD).hom)) := by
  apply (recordEquiv (targetModule A B) (targetModule A B)).injective
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  change (theta (targetModule A B) hD).linearEquiv z =
    ActualWeakModuleBraiding.braid B A
      (ActualWeakModuleBraiding.braid A B
        ((productHom hD (theta A hD).hom (theta B hD).hom).linearMap z))
  apply ActualWeakModuleBraiding.pair_induction A B
    (fun z => (theta (targetModule A B) hD).linearEquiv z =
      ActualWeakModuleBraiding.braid B A
        (ActualWeakModuleBraiding.braid A B
          ((productHom hD (theta A hD).hom (theta B hD).hom).linearMap z)))
  · simp
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro c d x y v
    rw [theta_product_tag]
    change thetaScalar (c+d) • tag A B c d x y v =
      ActualWeakModuleBraiding.braid B A (ActualWeakModuleBraiding.braid A B
        ((ActualWeakModuleIntertwinerRepresentability.inputMap hD A B A B
          (theta A hD).hom (theta B hD).hom).val
            (DirectSum.lof ℂ _ (PairSector A B) (c,d) (v ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] y)))))
    rw [inputMap_elementary, restrict_theta, restrict_theta]
    change thetaScalar (c+d) • tag A B c d x y v =
      ActualWeakModuleBraiding.braid B A (ActualWeakModuleBraiding.braid A B
        (tag A B c d (thetaScalar c • x) (thetaScalar d • y) v))
    have ht : tag A B c d (thetaScalar c • x) (thetaScalar d • y) v =
        (thetaScalar c * thetaScalar d) • tag A B c d x y v := by
      simp only [map_smul, LinearMap.smul_apply, smul_smul]
    rw [ht, map_smul, map_smul, ActualWeakModuleBraiding.braid_tag, map_smul,
      ActualWeakModuleBraiding.braid_tag]
    simp only [smul_smul]
    rw [thetaScalar_add hD]
    congr 1
    ring

end Product
end D5.S3.VertexAlgebra.Modules.ActualWeakModuleBalancing
