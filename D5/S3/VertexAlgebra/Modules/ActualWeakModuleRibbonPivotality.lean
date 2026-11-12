/- GID: D5/S3/VertexAlgebra/Modules/ActualWeakModuleRibbonPivotality
   mirror-B: D5/B/S3/VertexAlgebra/Modules/ActualWeakModuleRibbonPivotality
   status: source-only proposed proof bodies; native/kernel false. -/
/-
SOURCE IMPLEMENTATION ONLY. No native parsing, elaboration, or kernel check.
The original module, dual, tensorator, F, units, caps, braid, and twist are used.
The ordinary bidual supplier has a separate cast/direction repair overlay;
the original48 tensorator declarations remain unchanged.
-/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleBiduality
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleDualTensoratorUnit
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleRibbonTrace
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleRibbonDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleRibbonPivotality

open LatticeGeneratingFieldLocality LatticeDiscriminantTheta
open LatticeDualCosetModule LatticeDualCosetTransport LatticeChargedTransport
open LatticeChargedQuotientScalar (carry zeroCarry unitCharacter unitCharacter_nonzero)
open FullJacobiCurrentTransport FullJacobiIntertwiner
open ActualWeakModuleSectorCoordinates ActualWeakModuleClassification ActualWeakModuleHom
open ActualWeakModuleRealization ActualWeakModuleDuality ActualWeakModuleBiduality
open ActualWeakModuleUniversalField (P PairSector targetModule tag)
open ActualWeakModuleProductMultiplicity ActualWeakModuleProductNaturality
open ActualWeakModuleAssociator ActualWeakModulePentagon ActualWeakModuleUnits
open ActualWeakModuleUnitCoherence ActualWeakModuleDualTensorator
open ActualWeakModuleBalancing (theta thetaScalar restrict_theta)

open private restrict_extend from D5.S3.VertexAlgebra.Modules.ActualWeakModuleHom
open private restrict_identity from D5.S3.VertexAlgebra.Modules.ActualWeakModuleUnitCoherence
open private unitCharacter_square from D5.S3.VertexAlgebra.Sectors.LatticeChargedQuotientScalar
open private hom_ext_restrict bidualInverseFamily_left bidualInverseFamily_right from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleBiduality

universe u v w
variable {D : LatticeData}
attribute [local instance] Classical.propDecidable

section Scalar
variable (hD : (gramReal D).PosDef)

/-- The pivot fixed by the original cap and positive ribbon twist. -/
def pivotalScalar (c : Discriminant D) : ℂ :=
  unitCharacter D hD (-c) * F hD c (-c) c

theorem pivotalScalar_nonzero (c : Discriminant D) : pivotalScalar hD c ≠ 0 :=
  mul_ne_zero (unitCharacter_nonzero D hD (-c))
    (LatticeChargedQuotientScalar.associator_nonzero D hD c (-c) c)

@[simp] theorem pivotalScalar_zero : pivotalScalar hD (0 : Discriminant D) = 1 := by
  simp only [pivotalScalar, neg_zero, LatticeChargedQuotientScalar.unitCharacter_zero,
    F_unit_left, mul_one]

/-- Both factors are the ORIGINAL dual pentagon factors. -/
theorem pivotalScalar_dual (c : Discriminant D) :
    pivotalScalar hD c * pivotalScalar hD (-c) = 1 := by
  simpa only [pivotalScalar, neg_neg, mul_assoc, mul_left_comm, mul_comm] using
    cap_cup_left_normalization hD c

/-- This normalization comes from the actual closure, without a new hexagon. -/
theorem pivotalScalar_ribbon (c : Discriminant D) :
    pivotalScalar hD c = unitCharacter D hD (-c) *
      ActualWeakModuleBraiding.phase c (-c) * thetaScalar c / unitCharacter D hD c := by
  have hp := dual_pentagon hD c
  have hr := ActualWeakModuleRibbonTrace.ribbon_closure_factor hD c
  have hn := mul_ne_zero (unitCharacter_nonzero D hD c)
    (LatticeChargedQuotientScalar.associator_nonzero D hD (-c) c (-c))
  apply (mul_right_inj' hn).mp
  calc
    _ = unitCharacter D hD (-c) *
        (F hD c (-c) c * unitCharacter D hD c * F hD (-c) c (-c)) := by
      unfold pivotalScalar; ring
    _ = 1 := by rw [hp, unitCharacter_square]
    _ = (unitCharacter D hD (-c) * F hD (-c) c (-c) *
        ActualWeakModuleBraiding.phase c (-c) * thetaScalar c) *
          (unitCharacter D hD c / unitCharacter D hD c) := by
      rw [hr, div_self (unitCharacter_nonzero D hD c), mul_one]
    _ = _ := by ring

/-- A consumed elimination of exactly the three requested pentagons.
It retains F(c,d,0)=u(d)/u(c+d) and F(c,0,d)=u(c). -/
private theorem pivotal_F_defect (c d : Discriminant D) :
    F hD (c+d) (-(c+d)) (c+d) *
        (F hD (-d) (-c) (c+d) / F hD (-c) c d) =
      F hD c (-c) c * F hD d (-d) d *
        (unitCharacter D hD c * unitCharacter D hD (c+d) / unitCharacter D hD d) *
        (F hD c d (-(c+d)) / F hD d (-d) (-c)) := by
  have h₁ := LatticeChargedQuotientScalar.scalar_pentagon D hD d (-d) (-c) (c+d)
  have h₂ := LatticeChargedQuotientScalar.scalar_pentagon D hD c d (-(c+d)) (c+d)
  have h₃ := LatticeChargedQuotientScalar.scalar_pentagon D hD c (-c) c d
  have hn : -d + -c = -(c+d) := by abel
  have hc : d + -(c+d) = -c := by abel
  have hd : -c + (c+d) = d := by abel
  simp only [hn, hc, hd, add_neg_cancel, neg_add_cancel, F_unit_left,
    F_unit_middle, F_unit_right, one_mul] at h₁ h₂ h₃
  have h₂' : F hD c d (-(c+d)) * F hD c (-c) (c+d) *
      F hD d (-(c+d)) (c+d) * unitCharacter D hD (c+d) =
      F hD (c+d) (-(c+d)) (c+d) * unitCharacter D hD d := by
    calc
      _ = (F hD (c+d) (-(c+d)) (c+d) *
        (unitCharacter D hD d / unitCharacter D hD (c+d))) *
          unitCharacter D hD (c+d) := by rw [h₂]
      _ = _ := by field_simp [unitCharacter_nonzero D hD (c+d)]
  have he : F hD (c+d) (-(c+d)) (c+d) * F hD (-d) (-c) (c+d) *
      F hD d (-d) (-c) * unitCharacter D hD d =
      F hD c (-c) c * F hD d (-d) d * unitCharacter D hD c *
        unitCharacter D hD (c+d) * F hD c d (-(c+d)) * F hD (-c) c d := by
    calc
      _ = (F hD c d (-(c+d)) * F hD c (-c) (c+d) *
          F hD d (-(c+d)) (c+d) * unitCharacter D hD (c+d)) *
          F hD (-d) (-c) (c+d) * F hD d (-d) (-c) := by rw [h₂']; ring
      _ = F hD c d (-(c+d)) * F hD c (-c) (c+d) *
          unitCharacter D hD (c+d) *
          (F hD d (-d) (-c) * F hD d (-(c+d)) (c+d) *
            F hD (-d) (-c) (c+d)) := by ring
      _ = F hD c d (-(c+d)) * F hD c (-c) (c+d) *
          unitCharacter D hD (c+d) * F hD d (-d) d := by rw [h₁]
      _ = _ := by rw [← h₃]; ring
  field_simp [unitCharacter_nonzero D hD d,
    LatticeChargedQuotientScalar.associator_nonzero D hD (-c) c d,
    LatticeChargedQuotientScalar.associator_nonzero D hD d (-d) (-c)]
  linear_combination he

/-- The actual cochain law; neither p nor u is assumed multiplicative. -/
theorem pivotalScalar_cochain (c d : Discriminant D) :
    pivotalScalar hD (c+d) * k hD c d =
      pivotalScalar hD c * pivotalScalar hD d * k hD (-d) (-c) := by
  have hu : unitCharacter D hD (c+d) / unitCharacter D hD d =
      unitCharacter D hD d / unitCharacter D hD (c+d) := by
    apply (div_eq_div_iff (unitCharacter_nonzero D hD d)
      (unitCharacter_nonzero D hD (c+d))).mpr
    rw [unitCharacter_square, unitCharacter_square]
  calc
    _ = unitCharacter D hD (-c) * unitCharacter D hD (-d) *
        (F hD (c+d) (-(c+d)) (c+d) *
          (F hD (-d) (-c) (c+d) / F hD (-c) c d)) := by
      unfold pivotalScalar k
      field_simp [unitCharacter_nonzero D hD (-(c+d)),
        LatticeChargedQuotientScalar.associator_nonzero D hD (-c) c d] <;> ring
    _ = unitCharacter D hD (-c) * unitCharacter D hD (-d) *
        (F hD c (-c) c * F hD d (-d) d *
          (unitCharacter D hD c * (unitCharacter D hD (c+d) / unitCharacter D hD d)) *
          (F hD c d (-(c+d)) / F hD d (-d) (-c))) := by
      rw [pivotal_F_defect]; ring
    _ = _ := by
      rw [hu]
      unfold pivotalScalar k
      simp only [neg_neg, show -d + -c = -(c+d) by abel]
      field_simp [unitCharacter_nonzero D hD (c+d),
        LatticeChargedQuotientScalar.associator_nonzero D hD d (-d) (-c)] <;> ring

end Scalar

section Maps
variable {X : Type u} [AddCommGroup X] [Module ℂ X]
variable (A : FullJacobiLatticeModule D X) (hD : (gramReal D).PosDef)

/-- The bidual inclusion at the ACTUAL label c. Its input is precisely the
algebraic dual of the actual DA multiplicity at -c; no definitional neg_neg
identification is used. Consumed by the matching cap and finite cup sums. -/
private def bidualIota (c : Discriminant D) :
    Module.Dual ℂ (Multiplicity (dualModule A) (-c)) →ₗ[ℂ]
      Multiplicity (dualModule (dualModule A)) c :=
  iota (DualMultiplicity (dualModule A)) c

def pivotalFamily : Families A (dualModule (dualModule A)) :=
  fun c => pivotalScalar hD c • bidualFamily A hD c

def pivotalHom : ModuleHom A (dualModule (dualModule A)) :=
  extend hD (pivotalFamily A hD)

@[simp] theorem restrict_pivotalHom : restrict (pivotalHom A hD) = pivotalFamily A hD :=
  restrict_extend hD _

/-- The functional before the outer iota, with all neg_neg transport retained. -/
private theorem bidual_read (c : Discriminant D) (x : Multiplicity A c) :
    kappa (DualMultiplicity (dualModule A)) c (bidualFamily A hD c x) =
      (dualMultiplicityEquiv A hD c).dualMap (Module.Dual.eval ℂ (Multiplicity A c) x) := by
  simp only [bidualFamily, LinearMap.comp_apply, kappa_iota]

/-- Evaluation against EVERY original dual multiplicity, not a selected test. -/
private theorem bidual_read_apply (c : Discriminant D) (x : Multiplicity A c)
    (z : Multiplicity (dualModule A) (-c)) :
    kappa (DualMultiplicity (dualModule A)) c (bidualFamily A hD c x) z =
      dualMultiplicityEquiv A hD c z x := by
  rw [bidual_read]
  rfl

/-- A full original carrier readback of the scalar bidual. -/
private theorem pivotal_classified (c : Discriminant D) (x : Multiplicity A c)
    (v : Carrier D) :
    (pivotalHom A hD).linearMap (classified hD A c x v) =
      pivotalScalar hD c •
        classified hD (dualModule (dualModule A)) c (bidualFamily A hD c x) v := by
  rw [classified_natural, restrict_pivotalHom]
  simp only [pivotalFamily, LinearMap.smul_apply, classified,
    TensorProduct.tmul_smul, map_smul, LinearMap.comp_apply,
    LinearMap.flip_apply, TensorProduct.mk_apply]

end Maps

section Natural
variable {X : Type u} {Y : Type v}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable {A : FullJacobiLatticeModule D X} {B : FullJacobiLatticeModule D Y}
variable (hD : (gramReal D).PosDef)

private theorem restrict_comp {Z : Type w} [AddCommGroup Z] [Module ℂ Z]
    {C : FullJacobiLatticeModule D Z} (g : ModuleHom B C) (f : ModuleHom A B)
    (c : Discriminant D) (x : Multiplicity A c) :
    restrict (g.comp f) c x = restrict g c (restrict f c x) := rfl

/-- Naturality keeps the two original carrier universes independent. -/
theorem pivotalHom_natural (f : ModuleHom A B) :
    (pivotalHom B hD).comp f =
      (dualHom hD (dualHom hD f)).comp (pivotalHom A hD) := by
  apply hom_ext_restrict hD
  funext c
  apply LinearMap.ext
  intro x
  have h := congrArg (fun g => restrict g c x) (bidualHom_natural hD f)
  simp only [restrict_comp, bidualHom, restrict_extend] at h
  simp only [restrict_comp, restrict_pivotalHom, pivotalFamily, LinearMap.smul_apply,
    map_smul, h]

/-- Transpose is complex-linear precomposition on every functional. -/
private theorem transpose_read (f : ModuleHom A B) (c : Discriminant D)
    (z : Multiplicity (dualModule B) c) :
    kappa (DualMultiplicity A) c (restrict (dualHom hD f) c z) =
      (kappa (DualMultiplicity B) c z).comp (restrict f (-c)) := by
  obtain ⟨φ,rfl⟩ :=
    (ActualWeakModuleRealization.multiplicityEquiv (DualMultiplicity B) hD c).symm.surjective z
  simpa only [kappa_iota] using (dualHom_restrict hD f c φ)

end Natural

section DualCoherence
variable {X : Type u} [AddCommGroup X] [Module ℂ X]
variable (A : FullJacobiLatticeModule D X) (hD : (gramReal D).PosDef)

/-- The arbitrary-dimensional direction of bidual coherence; no reflexivity
or finiteness of the original multiplicities is needed. -/
theorem pivotalHom_dual :
    (dualHom hD (pivotalHom A hD)).comp (pivotalHom (dualModule A) hD) =
      ModuleHom.id (dualModule A) := by
  apply hom_ext_restrict hD
  funext c
  apply LinearMap.ext
  intro z
  apply (ActualWeakModuleRealization.multiplicityEquiv (DualMultiplicity A) hD c).injective
  apply LinearMap.ext
  intro x
  simp only [restrict_comp, restrict_identity, transpose_read, restrict_pivotalHom,
    pivotalFamily, LinearMap.smul_apply, map_smul, LinearMap.comp_apply,
    smul_eq_mul, bidual_read_apply]
  have hz : z = iota (DualMultiplicity A) c (kappa (DualMultiplicity A) c z) :=
    ((ActualWeakModuleRealization.multiplicityEquiv (DualMultiplicity A) hD c).symm_apply_apply z).symm
  rw [hz]
  simp only [dualMultiplicityEquiv_apply, dualKappa, bidualFamily, LinearMap.comp_apply,
    LinearEquiv.dualMap_apply, Module.Dual.eval_apply, kappa_iota, neg_neg,
    map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [← mul_assoc, pivotalScalar_dual, one_mul]

end DualCoherence

section FiniteIso
variable {X : Type u} [AddCommGroup X] [Module ℂ X]
variable (A : FullJacobiLatticeModule D X) (hD : (gramReal D).PosDef)
variable [∀ c : Discriminant D, Module.Finite ℂ (Multiplicity A c)]

def pivotalInverseFamily : Families (dualModule (dualModule A)) A :=
  fun c => (pivotalScalar hD c)⁻¹ • bidualInverseFamily A hD c

def pivotalInverseHom : ModuleHom (dualModule (dualModule A)) A :=
  extend hD (pivotalInverseFamily A hD)

private theorem pivotal_inverse_left :
    (pivotalInverseHom A hD).comp (pivotalHom A hD) = ModuleHom.id A := by
  apply hom_ext_restrict hD
  funext c
  apply LinearMap.ext
  intro x
  simp only [restrict_comp, pivotalInverseHom, restrict_extend, restrict_pivotalHom,
    pivotalInverseFamily, pivotalFamily, LinearMap.smul_apply, map_smul,
    smul_smul, inv_mul_cancel₀ (pivotalScalar_nonzero hD c), one_smul,
    bidualInverseFamily_left, restrict_identity]

private theorem pivotal_inverse_right :
    (pivotalHom A hD).comp (pivotalInverseHom A hD) =
      ModuleHom.id (dualModule (dualModule A)) := by
  apply hom_ext_restrict hD
  funext c
  apply LinearMap.ext
  intro x
  simp only [restrict_comp, pivotalInverseHom, restrict_extend, restrict_pivotalHom,
    pivotalInverseFamily, pivotalFamily, LinearMap.smul_apply, map_smul,
    smul_smul, mul_inv_cancel₀ (pivotalScalar_nonzero hD c), one_smul,
    bidualInverseFamily_right, restrict_identity]

/-- Only finite ORIGINAL multiplicities enter the inverse. -/
def pivotalIso : ModuleIso A (dualModule (dualModule A)) where
  linearEquiv :=
    { toLinearMap := (pivotalHom A hD).linearMap
      invFun := (pivotalInverseHom A hD).linearMap
      left_inv := fun x => congrArg (fun f : ModuleHom A A => f.linearMap x)
        (pivotal_inverse_left A hD)
      right_inv := fun z => congrArg (fun f : ModuleHom (dualModule (dualModule A))
        (dualModule (dualModule A)) => f.linearMap z) (pivotal_inverse_right A hD) }
  intertwines := (pivotalHom A hD).intertwines

end FiniteIso
end D5.S3.VertexAlgebra.Modules.ActualWeakModuleRibbonPivotality
