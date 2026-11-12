/- SOURCE ONLY / UNCOMPILED / UNACCEPTED.
No elaborator, compiler, kernel check, worktree, or native intake was used.
The full VOA/CFT/anomaly/fusion/string/AdS objective remains incomplete.

The endomorphism is the original productHom followed by both FORWARD braids.
The closure is the existing literal ribbonClosure, with its actual theta,
eta0, carry, epsilon, unitCharacter and associator normalization. Its scalar
is extracted at eta0; the finite sum is a theorem, not its definition.
Only actual multiplicities are assumed finite. Carrier, oscillators and P
are never assumed finite. Input universes remain independent, including
zero modules, zero multiplicities and rank zero. No pivotal structure,
pending bidual/tensorator/hexagon/character source, or analytic trace is used.

Attribution: the original lattice, full weak fields, classification, product,
ground exhaustion, forward braid and ribbon cancellation are the exact
suppliers pinned in prepared-inputs.json. Ordinary finite trace and its
tensor/conjugation laws are Mathlib's. All prerequisite acceptance statuses
remain as supplied; this file adds source scripts only.
-/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleRibbonTrace
import D5.S3.VertexAlgebra.Characters.LatticeDiscriminantWeil
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.RingTheory.TensorProduct.Finite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleHopfTrace

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeDiscriminantTheta LatticeDualCosetModule LatticeDualCosetTransport
open FullJacobiCurrentTransport FullJacobiIntertwiner FullJacobiTensorModule
open ActualCurrentTaylor ActualGroundJointWeights ActualGroundChargedSelection
open ActualWeakModuleSectorCoordinates ActualWeakModuleClassification
open ActualWeakModuleScalarProbes (sectorModule sectorModule_mode coordinate
  coordinate_apply tensorCoordinates tensorCoordinates_tmul)
open ActualWeakModuleHom (restrict)
open ActualWeakModuleUniversalField (P PairSector targetModule tag)
open ActualWeakModuleProductMultiplicity (PairMultiplicity Fiber FiberSum
  jAt jAt_val mu nu nu_lof mu_jAt multiplicityEquiv joint_single_charge
  joint_coordinate_exhaustion)
open ActualWeakModuleProductNaturality (productHom productHom_pair)
open ActualWeakModuleBraiding (braid braidIso braid_tag)
open ActualWeakModuleBalancing (double_phase)
open ActualWeakModuleDuality (discriminantSupport mem_discriminantSupport)
open ActualWeakModuleUnits (I eta0 etaCoefficient)
open ActualWeakModuleRibbonTrace (ribbonClosure ribbonClosure_linearMap
  ribbonTrace ribbonTrace_eq_sum)
open LatticeDiscriminantWeil (rho weilSplus)

open private jointWeightMap from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleHom
open private tensorOneHom from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleUnits
open private representative_weight_iff from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleRealization
open private currentState_single from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleClassification
open private restrict_identity from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleUnitCoherence

universe u v w
variable {D : LatticeData}
attribute [local instance] Classical.propDecidable

section ProductFiniteness
variable {X : Type u} {Y : Type v}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
variable (hD : (gramReal D).PosDef)
variable [∀ c : Discriminant D, Module.Finite ℂ (Multiplicity A c)]
variable [∀ d : Discriminant D, Module.Finite ℂ (Multiplicity B d)]

include hD in
/-- Finiteness of EVERY ACTUAL product multiplicity, transported through the
exact mu/nu equivalence, from finite tensor multiplicities on the finite fiber.
There is no finiteness assertion about the oscillator, Carrier or P. -/
theorem productMultiplicity_finite (e : Discriminant D) :
    Module.Finite ℂ (Multiplicity (targetModule A B) e) := by
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI : ∀ i : Fiber (D := D) e, Module.Finite ℂ (PairMultiplicity A B i.val) :=
    fun i => inferInstance
  letI : Module.Finite ℂ (FiberSum A B e) := inferInstance
  exact Module.Finite.equiv (multiplicityEquiv A B hD e).symm

end ProductFiniteness

section ActualEndomorphism
variable {X : Type u} {Y : Type v}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable {A : FullJacobiLatticeModule D X} {B : FullJacobiLatticeModule D Y}
variable (hD : (gramReal D).PosDef)

/-- Literal productHom, then forward A,B braid, then forward B,A braid. -/
def hopfEndomorphism (f : ModuleHom A A) (g : ModuleHom B B) :
    ModuleHom (targetModule A B) (targetModule A B) :=
  (braidIso B A).hom.comp ((braidIso A B).hom.comp (productHom hD f g))

/-- No carry or inverse transport is suppressed: v can be the original
ground = T_carry^-1([0]1). The two forward braids return that same carrier. -/
private theorem double_braid_pair (c d : Discriminant D) (v : Carrier D)
    (w : PairMultiplicity A B (c,d)) :
    braid B A (braid A B
      (DirectSum.lof ℂ _ (PairSector A B) (c,d) (v ⊗ₜ[ℂ] w))) =
      phase (pairing D c d) •
        DirectSum.lof ℂ _ (PairSector A B) (c,d) (v ⊗ₜ[ℂ] w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w z hw hz =>
      simpa only [TensorProduct.tmul_add, map_add, smul_add] using congrArg₂ (· + ·) hw hz
  | tmul x y =>
      change braid B A (braid A B (tag A B c d x y v)) =
        phase (pairing D c d) • tag A B c d x y v
      rw [braid_tag, map_smul, braid_tag, smul_smul, double_phase]

/-- Restriction on the ACTUAL jAt fiber. In particular the input still has
the exact inverse-vacuum and its epsilon factor in jAt_val. -/
theorem hopfEndomorphism_jAt (f : ModuleHom A A) (g : ModuleHom B B)
    (e : Discriminant D) (i : Fiber (D := D) e) (w : PairMultiplicity A B i.val) :
    restrict (hopfEndomorphism hD f g) e (jAt A B hD e i w) =
      phase (pairing D i.val.1 i.val.2) • jAt A B hD e i
        (TensorProduct.map (restrict f i.val.1) (restrict g i.val.2) w) := by
  apply Subtype.ext
  apply Subtype.ext
  change braid B A (braid A B
    ((productHom hD f g).linearMap (jAt A B hD e i w).val.val)) = _
  rw [jAt_val, productHom_pair, double_braid_pair]
  simp only [Submodule.coe_smul, jAt_val]

/-- The concrete block endomorphism, consumed immediately by exact conjugation
and the finite direct-sum trace. It is not a postulated product trace. -/
private def fiberHopf (f : ModuleHom A A) (g : ModuleHom B B) (e : Discriminant D) :
    FiberSum A B e →ₗ[ℂ] FiberSum A B e :=
  DirectSum.lmap (fun i : Fiber (D := D) e =>
    phase (pairing D i.val.1 i.val.2) •
      TensorProduct.map (restrict f i.val.1) (restrict g i.val.2))

/-- Full conjugation by the supplied exact productMultiplicityEquiv. The
original inverse-vacuum normalization is canceled ONLY by supplied mu_jAt. -/
private theorem hopfEndomorphism_conjugation (f : ModuleHom A A) (g : ModuleHom B B)
    (e : Discriminant D) :
    (multiplicityEquiv A B hD e).conj (restrict (hopfEndomorphism hD f g) e) =
      fiberHopf f g e := by
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro w
  change mu A B hD e
    (restrict (hopfEndomorphism hD f g) e (nu A B hD e (DirectSum.lof ℂ _ _ i w))) =
      DirectSum.lmap (fun k : Fiber (D := D) e =>
        phase (pairing D k.val.1 k.val.2) •
          TensorProduct.map (restrict f k.val.1) (restrict g k.val.2))
            (DirectSum.lof ℂ _ _ i w)
  rw [nu_lof, hopfEndomorphism_jAt, map_smul, mu_jAt, DirectSum.lmap_lof]
  simp only [LinearMap.smul_apply, map_smul]

end ActualEndomorphism

/-- Finite direct-sum trace, proved using the existing rectangular trace
cyclicity law. This helper is consumed by the actual fiber calculation below. -/
private theorem trace_directSum {ι : Type*} [Fintype ι]
    (V : ι → Type w) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, Module.Finite ℂ (V i)] (T : ∀ i, V i →ₗ[ℂ] V i) :
    LinearMap.trace ℂ (⨁ i, V i) (DirectSum.lmap T) =
      ∑ i, LinearMap.trace ℂ (V i) (T i) := by
  classical
  have hT : DirectSum.lmap T =
      ∑ i, (DirectSum.lof ℂ ι V i).comp
        ((T i).comp (DirectSum.component ℂ ι V i)) := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    change DirectSum.lmap T (DirectSum.lof ℂ ι V i x) =
      (∑ j, (DirectSum.lof ℂ ι V j).comp
        ((T j).comp (DirectSum.component ℂ ι V j))) (DirectSum.lof ℂ ι V i x)
    rw [DirectSum.lmap_lof, LinearMap.sum_apply, Finset.sum_eq_single i]
    · simp only [LinearMap.comp_apply, DirectSum.component.lof_self]
    · intro j hj hji
      simp [DirectSum.component.of, Ne.symm hji]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  rw [hT, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [LinearMap.trace_comp_comm'
    ((T i).comp (DirectSum.component ℂ ι V i)) (DirectSum.lof ℂ ι V i)]
  congr 1
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, DirectSum.component.lof_self]

section FiniteClosure
variable {X : Type u} {Y : Type v}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable {A : FullJacobiLatticeModule D X} {B : FullJacobiLatticeModule D Y}
variable (hD : (gramReal D).PosDef)
variable [∀ c : Discriminant D, Module.Finite ℂ (Multiplicity A c)]
variable [∀ d : Discriminant D, Module.Finite ℂ (Multiplicity B d)]

/-- Actual trace of the literal product endomorphism, from jAt conjugation,
finite direct-sum trace and the existing tensor-product trace theorem. -/
private theorem hopfEndomorphism_trace (f : ModuleHom A A) (g : ModuleHom B B) :
    (∑ e ∈ discriminantSupport hD,
      LinearMap.trace ℂ (Multiplicity (targetModule A B) e)
        (restrict (hopfEndomorphism hD f g) e)) =
      ∑ c ∈ discriminantSupport hD, ∑ d ∈ discriminantSupport hD,
        phase (pairing D c d) * LinearMap.trace ℂ (Multiplicity A c) (restrict f c) *
          LinearMap.trace ℂ (Multiplicity B d) (restrict g d) := by
  classical
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI : Fintype (Discriminant D) := Fintype.ofFinite _
  letI : ∀ e : Discriminant D, Module.Finite ℂ (Multiplicity (targetModule A B) e) :=
    productMultiplicity_finite A B hD
  have ht (e : Discriminant D) :
      LinearMap.trace ℂ (Multiplicity (targetModule A B) e)
        (restrict (hopfEndomorphism hD f g) e) =
      ∑ i : Fiber (D := D) e,
        phase (pairing D i.val.1 i.val.2) *
          LinearMap.trace ℂ (Multiplicity A i.val.1) (restrict f i.val.1) *
            LinearMap.trace ℂ (Multiplicity B i.val.2) (restrict g i.val.2) := by
    letI : AddCommGroup (Multiplicity (targetModule A B) e) :=
      Module.addCommMonoidToAddCommGroup ℂ (M := Multiplicity (targetModule A B) e)
    letI : AddCommGroup (FiberSum A B e) :=
      Module.addCommMonoidToAddCommGroup ℂ (M := FiberSum A B e)
    rw [← LinearMap.trace_conj' (R := ℂ)
      (M := Multiplicity (targetModule A B) e) (N := FiberSum A B e) (restrict (hopfEndomorphism hD f g) e)
      (multiplicityEquiv A B hD e), hopfEndomorphism_conjugation]
    unfold fiberHopf
    rw [trace_directSum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul, LinearMap.trace_tensorProduct', smul_eq_mul, mul_assoc]
  let reindex : (Σ e : Discriminant D, Fiber (D := D) e) ≃
      (Discriminant D × Discriminant D) :=
    { toFun := fun i => i.2.val
      invFun := fun cd => ⟨cd.1+cd.2, ⟨cd,rfl⟩⟩
      left_inv := by
        rintro ⟨e,⟨⟨c,d⟩,he⟩⟩
        subst e
        rfl
      right_inv := fun cd => rfl }
  change (∑ e : Discriminant D,
    LinearMap.trace ℂ (Multiplicity (targetModule A B) e)
      (restrict (hopfEndomorphism hD f g) e)) =
    ∑ c : Discriminant D, ∑ d : Discriminant D,
      phase (pairing D c d) * LinearMap.trace ℂ (Multiplicity A c) (restrict f c) *
        LinearMap.trace ℂ (Multiplicity B d) (restrict g d)
  simp_rw [ht]
  rw [← Fintype.sum_sigma' (fun (e : Discriminant D) (i : Fiber (D := D) e) =>
    phase (pairing D i.val.1 i.val.2) *
      LinearMap.trace ℂ (Multiplicity A i.val.1) (restrict f i.val.1) *
        LinearMap.trace ℂ (Multiplicity B i.val.2) (restrict g i.val.2))]
  calc
    _ = ∑ cd : Discriminant D × Discriminant D,
        phase (pairing D cd.1 cd.2) *
          LinearMap.trace ℂ (Multiplicity A cd.1) (restrict f cd.1) *
            LinearMap.trace ℂ (Multiplicity B cd.2) (restrict g cd.2) :=
      Fintype.sum_equiv reindex _ _ (fun i => rfl)
    _ = _ := Fintype.sum_prod_type _

/-- The actual cap/cup closure of the original endomorphism of P(A,B), using
the supplied ribbonClosure with its forward theta and actual eta0. -/
def hopfClosure (f : ModuleHom A A) (g : ModuleHom B B) : ModuleHom (I D) (I D) := by
  letI : ∀ e : Discriminant D, Module.Finite ℂ (Multiplicity (targetModule A B) e) :=
    productMultiplicity_finite A B hD
  exact ribbonClosure (targetModule A B) hD (hopfEndomorphism hD f g)

/-- FULL linear-map equality on the original unit Carrier, for arbitrary
original module endomorphisms. The oscillator is not being traced. -/
theorem hopfClosure_linearMap (f : ModuleHom A A) (g : ModuleHom B B) :
    (hopfClosure hD f g).linearMap =
      (∑ c ∈ discriminantSupport hD, ∑ d ∈ discriminantSupport hD,
        phase (pairing D c d) * LinearMap.trace ℂ (Multiplicity A c) (restrict f c) *
          LinearMap.trace ℂ (Multiplicity B d) (restrict g d)) •
            (LinearMap.id : Carrier D →ₗ[ℂ] Carrier D) := by
  letI : ∀ e : Discriminant D, Module.Finite ℂ (Multiplicity (targetModule A B) e) :=
    productMultiplicity_finite A B hD
  change (ribbonClosure (targetModule A B) hD (hopfEndomorphism hD f g)).linearMap = _
  rw [ribbonClosure_linearMap, hopfEndomorphism_trace]

/-- Scalar extraction through the original eta0 and etaCoefficient, AFTER
the literal composite. The phase sum is not used in this definition. -/
def hopfScalar (f : ModuleHom A A) (g : ModuleHom B B) : ℂ :=
  etaCoefficient hD (restrict (hopfClosure hD f g) 0 (eta0 hD))

theorem hopfScalar_eq_sum (f : ModuleHom A A) (g : ModuleHom B B) :
    hopfScalar hD f g =
      ∑ c ∈ discriminantSupport hD, ∑ d ∈ discriminantSupport hD,
        phase (pairing D c d) * LinearMap.trace ℂ (Multiplicity A c) (restrict f c) *
          LinearMap.trace ℂ (Multiplicity B d) (restrict g d) := by
  have hr : restrict (hopfClosure hD f g) 0 (eta0 hD) =
      (∑ c ∈ discriminantSupport hD, ∑ d ∈ discriminantSupport hD,
        phase (pairing D c d) * LinearMap.trace ℂ (Multiplicity A c) (restrict f c) *
          LinearMap.trace ℂ (Multiplicity B d) (restrict g d)) • eta0 hD := by
    apply Subtype.ext
    apply Subtype.ext
    change (hopfClosure hD f g).linearMap (eta0 hD).val.val = _
    exact LinearMap.congr_fun (hopfClosure_linearMap hD f g) (eta0 hD).val.val
  unfold hopfScalar
  rw [hr, map_smul, ActualWeakModuleUnits.etaCoefficient_eta0, smul_eq_mul, mul_one]

end FiniteClosure

section OriginalChargeSectors
variable (hD : (gramReal D).PosDef)

/-- Vacuum in the ACTUAL original representative sector, as a joint weight
in its original positive-current kernel. No substitute sector record is made. -/
private def sectorVacuum (a : Discriminant D) :
    Multiplicity (sectorModule D (representative D a)) a := by
  have hc (i : Fin D.rank) (m : ℤ) :
      current (sectorModule D (representative D a)) i m
        (Finsupp.single 0 (1 : Oscillator D)) =
      Finsupp.single 0 (shiftedCurrentPolynomial D (representative D a) 1 i 0 m 1) := by
    rw [current, currentState_single, sectorModule_mode, action_current_coefficients]
  have ho : Finsupp.single 0 (1 : Oscillator D) ∈
      Omega (sectorModule D (representative D a)) := by
    apply (mem_Omega _ _).mpr
    intro i r
    rw [hc]
    simp [shiftedCurrentPolynomial, show ¬ ((r : ℤ)+1 < 0) by omega,
      show (r : ℤ)+1 ≠ 0 by omega]
  refine ⟨⟨Finsupp.single 0 1, ho⟩, (mem_jointWeight_iff _ _ _).mpr ?_⟩
  intro i
  change current (sectorModule D (representative D a)) i 0
    (Finsupp.single 0 (1 : Oscillator D)) = _
  rw [hc]
  simp [shiftedCurrentPolynomial, Finsupp.smul_single, bilinear]

private def sectorCoefficient (a : Discriminant D) :
    Multiplicity (sectorModule D (representative D a)) a →ₗ[ℂ] ℂ :=
  (coordinate D (0,0)).comp
    ((Omega (sectorModule D (representative D a))).subtype.comp
      (jointWeight (sectorModule D (representative D a)) (representative D a)).subtype)

include hD in
/-- Wrong actual sector multiplicities vanish by the supplied ground
exhaustion and the exact representative/Gram equation, including rank zero. -/
private theorem sector_multiplicity_wrong (a c : Discriminant D) (hc : c ≠ a)
    (w : Multiplicity (sectorModule D (representative D a)) c) : w = 0 := by
  let z := jointWeightMap (tensorOneHom (D := D) (representative D a))
    (representative D c) w
  have impossible (l : Charge D) :
      representative D a + gramMap D l ≠ representative D c := by
    intro he
    exact hc (((representative_weight_iff hD c a l).mp he).1.symm)
  apply Subtype.ext
  apply Subtype.ext
  apply Finsupp.ext
  intro l
  apply MvPolynomial.ext
  intro d
  have hz := joint_coordinate_exhaustion hD (representative D a)
    (representative D c) z (l,d) (Or.inr (impossible l))
  change tensorCoordinates (w.val.val ⊗ₜ[ℂ] (1 : ℂ)) (l,d) = 0 at hz
  simpa [tensorCoordinates_tmul, coordinate_apply] using hz

include hD in
/-- The missing dimension-one proof is actual coordinate reconstruction,
not a dimension hypothesis. Scalar tensor removal uses the existing rid. -/
private theorem sector_multiplicity_reconstruct (a : Discriminant D)
    (w : Multiplicity (sectorModule D (representative D a)) a) :
    w.val.val = sectorCoefficient a w • (sectorVacuum a).val.val := by
  let z := jointWeightMap (tensorOneHom (D := D) (representative D a))
    (representative D a) w
  have unique (l : Charge D) :
      representative D a + gramMap D l = representative D a ↔ l = 0 := by
    simpa using representative_weight_iff hD a a l
  have hs := joint_single_charge hD (representative D a) (representative D a) 0 unique z
  change w.val.val ⊗ₜ[ℂ] (1 : ℂ) = Finsupp.single 0 (1 : Oscillator D) ⊗ₜ[ℂ]
    tensorCoordinates (w.val.val ⊗ₜ[ℂ] (1 : ℂ)) (0,0) at hs
  have hr := congrArg (fun t : Carrier D ⊗[ℂ] ℂ => TensorProduct.rid ℂ (Carrier D) t) hs
  simpa [sectorCoefficient, sectorVacuum, tensorCoordinates_tmul,
    coordinate_apply, TensorProduct.rid_tmul] using hr

private def sectorMultiplicityEquiv (a : Discriminant D) :
    Multiplicity (sectorModule D (representative D a)) a ≃ₗ[ℂ] ℂ where
  toLinearMap := sectorCoefficient a
  invFun t := t • sectorVacuum a
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    exact (sector_multiplicity_reconstruct hD a w).symm
  right_inv t := by
    simp [sectorCoefficient, sectorVacuum, ActualWeakModuleScalarProbes.coordinate, coordinate_apply]

include hD in
/-- Actual multiplicity finiteness for each ORIGINAL canonical charge sector. -/
theorem sectorMultiplicity_finite (a c : Discriminant D) :
    Module.Finite ℂ (Multiplicity (sectorModule D (representative D a)) c) := by
  classical
  by_cases hc : c = a
  · subst c
    exact Module.Finite.equiv (sectorMultiplicityEquiv hD a).symm
  · letI : Subsingleton (Multiplicity (sectorModule D (representative D a)) c) :=
      ⟨fun x y => by
        rw [sector_multiplicity_wrong hD a c hc x, sector_multiplicity_wrong hD a c hc y]⟩
    infer_instance

include hD in
/-- Dimension delta for the actual joint-weight multiplicities, derived
from ground exhaustion and the original representative sector field. -/
theorem sectorMultiplicity_finrank (a c : Discriminant D) :
    Module.finrank ℂ (Multiplicity (sectorModule D (representative D a)) c) =
      if c = a then 1 else 0 := by
  classical
  by_cases hc : c = a
  · subst c
    simpa using (sectorMultiplicityEquiv hD a).finrank_eq
  · letI : Subsingleton (Multiplicity (sectorModule D (representative D a)) c) :=
      ⟨fun x y => by
        rw [sector_multiplicity_wrong hD a c hc x, sector_multiplicity_wrong hD a c hc y]⟩
    rw [if_neg hc]
    exact Module.finrank_zero_of_subsingleton

/-- Actual extracted Hopf scalar for identity maps of the ORIGINAL sectors. -/
def sectorHopfScalar (a b : Discriminant D) : ℂ := by
  letI : ∀ c, Module.Finite ℂ
      (Multiplicity (sectorModule D (representative D a)) c) := sectorMultiplicity_finite hD a
  letI : ∀ d, Module.Finite ℂ
      (Multiplicity (sectorModule D (representative D b)) d) := sectorMultiplicity_finite hD b
  exact hopfScalar hD (ModuleHom.id (sectorModule D (representative D a)))
    (ModuleHom.id (sectorModule D (representative D b)))

/-- Both braids are forward: the literal sector scalar has the POSITIVE
pairing phase. This is not the negative WeilS kernel. -/
theorem sectorHopfScalar_eq_phase (a b : Discriminant D) :
    sectorHopfScalar hD a b = phase (pairing D a b) := by
  letI : ∀ c, Module.Finite ℂ
      (Multiplicity (sectorModule D (representative D a)) c) := sectorMultiplicity_finite hD a
  letI : ∀ d, Module.Finite ℂ
      (Multiplicity (sectorModule D (representative D b)) d) := sectorMultiplicity_finite hD b
  have hA (c : Discriminant D) :
      restrict (ModuleHom.id (sectorModule D (representative D a))) c = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact restrict_identity c x
  have hB (d : Discriminant D) :
      restrict (ModuleHom.id (sectorModule D (representative D b))) d = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact restrict_identity d x
  unfold sectorHopfScalar
  rw [hopfScalar_eq_sum]
  simp_rw [hA, hB, LinearMap.trace_id, sectorMultiplicity_finrank hD]
  simp [mul_ite, ite_mul, mem_discriminantSupport]

end OriginalChargeSectors

section NormalizedOperator
variable (D : LatticeData) [hD : Fact (gramReal D).PosDef]
local instance : Fintype (Discriminant D) := Fintype.ofFinite _

/-- Original rho normalization of ACTUAL extracted charge-sector Hopf scalars,
as a linear map on the WHOLE finite function space. -/
def normalizedHopfOperator : (Discriminant D → ℂ) →ₗ[ℂ] (Discriminant D → ℂ) where
  toFun f a := (rho D)⁻¹ * ∑ b, sectorHopfScalar hD.out a b * f b
  map_add' f g := by ext a; simp [mul_add, Finset.sum_add_distrib]
  map_smul' z f := by ext a; simp [Finset.mul_sum, mul_left_comm, mul_assoc]

/-- The full function-space operator is exactly the EXISTING positive Weil
transform. Its orthogonality and inverse theory remain the existing finite
Weil theory; no second Fourier theory or modular-relations wrapper is added. -/
theorem normalizedHopfOperator_eq_weilSplus :
    normalizedHopfOperator D = weilSplus D := by
  apply LinearMap.ext
  intro f
  funext a
  change (rho D)⁻¹ * (∑ b, sectorHopfScalar hD.out a b * f b) =
    (rho D)⁻¹ * ∑ b, pairingCharacter D hD.out a b * f b
  simp_rw [sectorHopfScalar_eq_phase]
  rfl

end NormalizedOperator
end D5.S3.VertexAlgebra.Modules.ActualWeakModuleHopfTrace
