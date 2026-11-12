/-
SOURCE_ONLY_UNCOMPILED_UNACCEPTED. No elaborator, kernel or axiom-closure claim.
The full original VOA/CFT/fusion/string goal remains ACTIVE / INCOMPLETE.

Inverse-half extraction for arbitrary ORIGINAL full weak modules, in three
independent universes. The actual accepted classification and faithful Hom API
are consumed at their pinned final99 sources. ActualWeakModuleFullIntertwiner
is source-only, and ActualWeakTargetFullFusion is the ORIGINAL source candidate
whose native check is pending elsewhere. No live peer artifact is consumed.
The normalized transport dependency is the separately pinned ACCEPTED final.

Every multiplicity is a variable in the actual joint-weight subtype. No basis,
finite dimension, nonzero vector, injectivity premise, uniform Hahn support,
or arbitrary-input representation theorem is assumed. The only new objects
are actual sector inclusions, restrictions, and a bilinear family of sector
Homs. There is no new universal-field or representing-object model here.

Attribution: accepted classification/Hom/tensor/direct-sum suppliers; Scott
Carnahan's Hahn/residue API; Bakalov--Kac math/0402315v1 section 4.1 for the
charged conventions; Kalle Kytölä's conformal calculus. The recovered complete
Pro answer, sections 7.1--7.3 and 8.2, supplies conditional mathematical advice,
with the parent's corrections: arbitrary u/v are in X/Y and translations are
the actual omega(D,H) zero modes. It supplies no kernel evidence.
-/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleFullIntertwiner
import D5.S3.VertexAlgebra.Sectors.ActualWeakTargetFullFusion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleIntertwinerExtraction

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeDiscriminantTheta LatticeDualCosetModule
open FullJacobiCurrentTransport (FullJacobiLatticeModule)
open FullJacobiIntertwiner (ModuleHom)
open ActualWeakModuleSectorCoordinates (Multiplicity Sector Model)
open ActualWeakModuleClassification (classificationEquiv inverseGram)
open ActualWeakModuleHom (homSpace recordEquiv)


universe uX uY uZ uX' uY' uZ'
variable {D : LatticeData}
variable {X : Type uX} {Y : Type uY} {Z : Type uZ}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable [AddCommGroup Z] [Module ℂ Z]

attribute [local instance] Classical.propDecidable

/-- The original scalar sector, through the actual classification, at an
arbitrary multiplicity vector. The output is the faithful full Hom subtype. -/
def inclusionLinear (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (c : Discriminant D) :
    Multiplicity A c →ₗ[ℂ]
      homSpace (Sectors.ActualWeakTargetFullIntertwiner.scalarModule D (representative D c)) A where
  toFun n :=
    ⟨(classificationEquiv A positiveG).toLinearMap.comp
      ((DirectSum.lof ℂ (Discriminant D) (Sector A) c).comp
        ((TensorProduct.mk ℂ (Carrier D) (Multiplicity A c)).flip n)), by
      intro h r s
      change classificationEquiv A positiveG
        (DirectSum.lof ℂ (Discriminant D) (Sector A) c
          (FullJacobiCurrentTransport.mode
            (Sectors.ActualWeakTargetFullIntertwiner.scalarModule D (representative D c)) h r s ⊗ₜ[ℂ] n)) = _
      simpa only [ActualWeakModuleClassification.canonicalModule,
        FullJacobiDirectSum.directSumModule_mode, DirectSum.lmap_lof,
        FullJacobiTensorModule.tensorModule_mode, TensorProduct.map_tmul,
        LinearMap.id_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.coe_toLinearMap, TensorProduct.mk_apply,
        LinearMap.flip_apply, FullJacobiCurrentTransport.mode,
        Sectors.ActualWeakTargetFullIntertwiner.scalarModule] using
          (ActualWeakModuleClassification.classification A positiveG h r
            (DirectSum.lof ℂ (Discriminant D) (Sector A) c (s ⊗ₜ[ℂ] n)))⟩
  map_add' n n' := by
    apply Subtype.ext
    apply LinearMap.ext
    intro s
    change classificationEquiv A positiveG
      (DirectSum.lof ℂ (Discriminant D) (Sector A) c (s ⊗ₜ[ℂ] (n+n'))) =
        classificationEquiv A positiveG
          (DirectSum.lof ℂ (Discriminant D) (Sector A) c (s ⊗ₜ[ℂ] n)) +
        classificationEquiv A positiveG
          (DirectSum.lof ℂ (Discriminant D) (Sector A) c (s ⊗ₜ[ℂ] n'))
    simp only [TensorProduct.tmul_add, map_add]
  map_smul' a n := by
    apply Subtype.ext
    apply LinearMap.ext
    intro s
    change classificationEquiv A positiveG
      (DirectSum.lof ℂ (Discriminant D) (Sector A) c (s ⊗ₜ[ℂ] (a • n))) =
        a • classificationEquiv A positiveG
          (DirectSum.lof ℂ (Discriminant D) (Sector A) c (s ⊗ₜ[ℂ] n))
    simp only [TensorProduct.tmul_smul, map_smul]

/-- This is an original ModuleHom, with all original states and integer modes. -/
def inclusionHom (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (c : Discriminant D) (n : Multiplicity A c) :
    ModuleHom (Sectors.ActualWeakTargetFullIntertwiner.scalarModule D (representative D c)) A :=
  (recordEquiv _ A).symm (inclusionLinear positiveG A c n)

@[simp] theorem inclusion_apply (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (c : Discriminant D)
    (n : Multiplicity A c) (s : Carrier D) :
    (inclusionLinear positiveG A c n).val s = classificationEquiv A positiveG
      (DirectSum.lof ℂ (Discriminant D) (Sector A) c (s ⊗ₜ[ℂ] n)) := rfl

theorem inclusion_mode (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (c : Discriminant D)
    (n : Multiplicity A c) (h : Carrier D) (r : ℤ) (s : Carrier D) :
    (inclusionLinear positiveG A c n).val
        (((action D (representative D c) h)[[r]]) s) =
      ((A.stateField h)[[r]]) ((inclusionLinear positiveG A c n).val s) :=
  (inclusionLinear positiveG A c n).property h r s

/-- Actual finite per-vector generation, from Theta's inverse, not a
decomposition axiom. The tensor induction is algebraic, with variable n.
The outer sum is over the finite support of this particular inverse image. -/
theorem induction_on_inclusions (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (x : X) (P : X → Prop)
    (hzero : P 0) (hadd : ∀ x y, P x → P y → P (x+y))
    (hsector : ∀ c n s, P ((inclusionLinear positiveG A c n).val s)) : P x := by
  classical
  let v : Model A := (classificationEquiv A positiveG).symm x
  have ht (c : Discriminant D) (t : Sector A c) :
      P (classificationEquiv A positiveG
        (DirectSum.lof ℂ (Discriminant D) (Sector A) c t)) := by
    induction t using TensorProduct.inductionOn with
    | tmul s n => exact hsector c n s
    | add t t' ht ht' =>
      simpa only [map_add] using hadd _ _ ht ht'
  have hs (s : Finset (Discriminant D)) :
      P (∑ c ∈ s, classificationEquiv A positiveG
        (DirectSum.lof ℂ (Discriminant D) (Sector A) c (v c))) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using hzero
    | @insert c s hc ih =>
      rw [Finset.sum_insert hc]
      exact hadd _ _ (ht c (v c)) ih
  have expansion : (∑ c ∈ v.support,
      DirectSum.lof ℂ (Discriminant D) (Sector A) c (v c)) = v := by
    simpa only [DirectSum.lof_eq_of] using DirectSum.sum_support_of v
  have hx : (∑ c ∈ v.support, classificationEquiv A positiveG
      (DirectSum.lof ℂ (Discriminant D) (Sector A) c (v c))) = x := by
    rw [← map_sum, expansion]
    exact (classificationEquiv A positiveG).apply_symm_apply x
  exact hx ▸ hs v.support

/-- The exact original generic field space, with no field representation
condition added to its carrier. -/
abbrev FullFields (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) :=
  ActualWeakModuleFullIntertwiner.operatorSpace A B J (inverseGram positiveG)

/-- Generic lawful restriction followed by the identity-on-fields sector
readback. Linearity here is in the entire original field I. -/
def restriction (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) (c d : Discriminant D)
    (n : Multiplicity A c) (m : Multiplicity B d) :
    FullFields positiveG A B J →ₗ[ℂ]
      Sectors.ActualWeakTargetFullFusion.FullFields positiveG (representative D c) (representative D d) J :=
  (ActualWeakModuleFullIntertwiner.sectorReadback (representative D c) (representative D d)
    (inverseGram positiveG) J).toLinearMap.comp
      (ActualWeakModuleFullIntertwiner.restrictionLinear (J := J) (inverseGram positiveG)
        (inclusionLinear positiveG A c n) (inclusionLinear positiveG B d m))

@[simp] theorem restriction_coeff (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) (c d : Discriminant D)
    (n : Multiplicity A c) (m : Multiplicity B d) (I : FullFields positiveG A B J)
    (s t : Carrier D) (q : ℚ) :
    (((restriction positiveG A B J c d n m I).val s).coeff q t) =
      (I.val ((inclusionLinear positiveG A c n).val s)).coeff q
        ((inclusionLinear positiveG B d m).val t) := by
  change (((ActualWeakModuleFullIntertwiner.map (inverseGram positiveG)
    (inclusionHom positiveG A c n) (inclusionHom positiveG B d m)
    (ModuleHom.id J) I).val s).coeff q t) = _
  exact ActualWeakModuleFullIntertwiner.map_coeff (inverseGram positiveG)
    (inclusionHom positiveG A c n) (inclusionHom positiveG B d m)
    (ModuleHom.id J) I s t q

theorem restriction_mode (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) (c d : Discriminant D)
    (n : Multiplicity A c) (m : Multiplicity B d) (I : FullFields positiveG A B J)
    (s t : Carrier D) (τ : ℚ) :
    Sectors.ActualWeakTargetFullIntertwiner.mode (restriction positiveG A B J c d n m I).val s τ t =
      ActualWeakModuleFullIntertwiner.mode I.val ((inclusionLinear positiveG A c n).val s) τ
        ((inclusionLinear positiveG B d m).val t) :=
  restriction_coeff positiveG A B J c d n m I s t (-τ-1)

/-- Literal equality of coefficient supports and the original pointwise PWO
property. No support is taken uniformly over n, m, s, t, or I. -/
theorem restriction_support (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) (c d : Discriminant D)
    (n : Multiplicity A c) (m : Multiplicity B d) (I : FullFields positiveG A B J)
    (s t : Carrier D) :
    Function.support (fun q => ((restriction positiveG A B J c d n m I).val s).coeff q t) =
        Function.support (fun q => (I.val ((inclusionLinear positiveG A c n).val s)).coeff q
          ((inclusionLinear positiveG B d m).val t)) ∧
      (Function.support (fun q =>
        ((restriction positiveG A B J c d n m I).val s).coeff q t)).IsPWO := by
  have he : (fun q => ((restriction positiveG A B J c d n m I).val s).coeff q t) =
      (fun q => (I.val ((inclusionLinear positiveG A c n).val s)).coeff q
        ((inclusionLinear positiveG B d m).val t)) :=
    funext (fun q => restriction_coeff positiveG A B J c d n m I s t q)
  refine ⟨congrArg Function.support he, ?_⟩
  rw [he]
  exact (I.val ((inclusionLinear positiveG A c n).val s)).isPWO_support_coeff
    ((inclusionLinear positiveG B d m).val t)

section RestrictionLaws
variable (positiveG : (gramReal D).PosDef)
variable (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
variable (J : FullJacobiLatticeModule D Z) (c d : Discriminant D)
variable (n : Multiplicity A c) (m : Multiplicity B d) (I : FullFields positiveG A B J)

/-- Both translation identities use the actual omega0 translations. The
sector source/input translations are the literal moduleL(-1) readback. -/
theorem restriction_source (s : Carrier D) (τ : ℚ) :
    Sectors.ActualWeakTargetFullIntertwiner.mode (restriction positiveG A B J c d n m I).val
        (LatticeDualCosetConformal.moduleL D (representative D c) (inverseGram positiveG) (-1) s) τ =
      -(τ : ℂ) • Sectors.ActualWeakTargetFullIntertwiner.mode (restriction positiveG A B J c d n m I).val s (τ-1) :=
  (restriction positiveG A B J c d n m I).property.source s τ

theorem restriction_target (s : Carrier D) (τ : ℚ) :
    (Sectors.ActualWeakTargetFullIntertwiner.targetTranslation J (inverseGram positiveG)).comp
        (Sectors.ActualWeakTargetFullIntertwiner.mode (restriction positiveG A B J c d n m I).val s τ) -
      (Sectors.ActualWeakTargetFullIntertwiner.mode (restriction positiveG A B J c d n m I).val s τ).comp
        (LatticeDualCosetConformal.moduleL D (representative D d) (inverseGram positiveG) (-1)) =
      -(τ : ℂ) • Sectors.ActualWeakTargetFullIntertwiner.mode (restriction positiveG A B J c d n m I).val s (τ-1) :=
  (restriction positiveG A B J c d n m I).property.target s τ

/-- Three literal family identities; in particular no cancellation is used
to infer either of the two right-hand finite supports. -/
theorem restriction_terms (h s t : Carrier D) (p r : ℤ) (τ : ℚ) (i : ℕ) :
    Sectors.ActualWeakTargetFullIntertwiner.leftTerm D (representative D c)
        (restriction positiveG A B J c d n m I).val h s t p r τ i =
      ActualWeakModuleFullIntertwiner.leftTerm A I.val h ((inclusionLinear positiveG A c n).val s)
        ((inclusionLinear positiveG B d m).val t) p r τ i ∧
    Sectors.ActualWeakTargetFullIntertwiner.firstTerm D J (restriction positiveG A B J c d n m I).val h s t p r τ i =
      ActualWeakModuleFullIntertwiner.firstTerm J I.val h ((inclusionLinear positiveG A c n).val s)
        ((inclusionLinear positiveG B d m).val t) p r τ i ∧
    Sectors.ActualWeakTargetFullIntertwiner.secondTerm D (representative D d)
        (restriction positiveG A B J c d n m I).val h s t p r τ i =
      ActualWeakModuleFullIntertwiner.secondTerm B I.val h ((inclusionLinear positiveG A c n).val s)
        ((inclusionLinear positiveG B d m).val t) p r τ i := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Sectors.ActualWeakTargetFullIntertwiner.leftTerm, ActualWeakModuleFullIntertwiner.leftTerm, restriction_mode, inclusion_mode]
  · simp only [Sectors.ActualWeakTargetFullIntertwiner.firstTerm, ActualWeakModuleFullIntertwiner.firstTerm, restriction_mode]
  · simp only [Sectors.ActualWeakTargetFullIntertwiner.secondTerm, ActualWeakModuleFullIntertwiner.secondTerm, restriction_mode, inclusion_mode]

/-- All three finite supports and their exact signed finsum equality. This
proof transports the ORIGINAL vectorwise law, without a new support axiom. -/
theorem restriction_jacobi (h s t : Carrier D) (p r : ℤ) (τ : ℚ) :
    Function.HasFiniteSupport (Sectors.ActualWeakTargetFullIntertwiner.leftTerm D (representative D c)
      (restriction positiveG A B J c d n m I).val h s t p r τ) ∧
    Function.HasFiniteSupport (Sectors.ActualWeakTargetFullIntertwiner.firstTerm D J
      (restriction positiveG A B J c d n m I).val h s t p r τ) ∧
    Function.HasFiniteSupport (Sectors.ActualWeakTargetFullIntertwiner.secondTerm D (representative D d)
      (restriction positiveG A B J c d n m I).val h s t p r τ) ∧
      (∑ᶠ i : ℕ, Sectors.ActualWeakTargetFullIntertwiner.leftTerm D (representative D c)
        (restriction positiveG A B J c d n m I).val h s t p r τ i) =
      (∑ᶠ i : ℕ, Sectors.ActualWeakTargetFullIntertwiner.firstTerm D J
        (restriction positiveG A B J c d n m I).val h s t p r τ i) -
      (∑ᶠ i : ℕ, Sectors.ActualWeakTargetFullIntertwiner.secondTerm D (representative D d)
        (restriction positiveG A B J c d n m I).val h s t p r τ i) := by
  have hL := funext (fun i => (restriction_terms positiveG A B J c d n m I h s t p r τ i).1)
  have hF := funext (fun i => (restriction_terms positiveG A B J c d n m I h s t p r τ i).2.1)
  have hS := funext (fun i => (restriction_terms positiveG A B J c d n m I h s t p r τ i).2.2)
  simp_rw [hL, hF, hS]
  exact I.property.jacobi h ((inclusionLinear positiveG A c n).val s)
    ((inclusionLinear positiveG B d m).val t) p r τ

end RestrictionLaws

/-- A genuinely bilinear dependence on the two actual multiplicities,
before applying any sector inverse. -/
def restrictionBilinear (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) (I : FullFields positiveG A B J)
    (c d : Discriminant D) :
    Multiplicity A c →ₗ[ℂ] Multiplicity B d →ₗ[ℂ]
      Sectors.ActualWeakTargetFullFusion.FullFields positiveG (representative D c) (representative D d) J where
  toFun n :=
    { toFun m := restriction positiveG A B J c d n m I
      map_add' m m' := by
        simp only [restriction, map_add, LinearMap.comp_apply, LinearMap.add_apply]
      map_smul' a m := by
        simp only [restriction, map_smul, LinearMap.comp_apply, LinearMap.smul_apply,
          RingHom.id_apply] }
  map_add' n n' := by
    apply LinearMap.ext
    intro m
    simp only [restriction, map_add, LinearMap.comp_apply, LinearMap.add_apply]
    rfl
  map_smul' a n := by
    apply LinearMap.ext
    intro m
    simp only [restriction, map_smul, LinearMap.comp_apply, LinearMap.smul_apply,
      RingHom.id_apply]
    rfl

/-- The requested exact bilinear Hom family. The inverse is the original
sector fusion inverse, not a chosen field equivalence or a bidual map. -/
def sectorHomBilinear (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) (I : FullFields positiveG A B J)
    (c d : Discriminant D) :
    Multiplicity A c →ₗ[ℂ] Multiplicity B d →ₗ[ℂ]
      Sectors.ActualWeakTargetFullFusion.Hom (representative D c + representative D d) J where
  toFun n := (Sectors.ActualWeakTargetFullFusion.inverseLinear positiveG (representative D c) (representative D d) J).comp
    (restrictionBilinear positiveG A B J I c d n)
  map_add' n n' := by
    apply LinearMap.ext
    intro m
    simp only [LinearMap.comp_apply, map_add, LinearMap.add_apply]
  map_smul' a n := by
    apply LinearMap.ext
    intro m
    simp only [LinearMap.comp_apply, map_smul, LinearMap.smul_apply, RingHom.id_apply]

/-- The family is LINEAR in I and bilinear in variable n,m; no finiteness
or common-support condition is imposed on this product of Hom spaces. -/
def extractionLinear (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) :
    FullFields positiveG A B J →ₗ[ℂ]
      ∀ c d : Discriminant D, Multiplicity A c →ₗ[ℂ] Multiplicity B d →ₗ[ℂ]
        Sectors.ActualWeakTargetFullFusion.Hom (representative D c + representative D d) J where
  toFun I := sectorHomBilinear positiveG A B J I
  map_add' I K := by
    funext c d
    apply LinearMap.ext
    intro n
    apply LinearMap.ext
    intro m
    change Sectors.ActualWeakTargetFullFusion.inverseLinear positiveG _ _ J
      (restriction positiveG A B J c d n m (I+K)) =
        Sectors.ActualWeakTargetFullFusion.inverseLinear positiveG _ _ J
          (restriction positiveG A B J c d n m I) +
        Sectors.ActualWeakTargetFullFusion.inverseLinear positiveG _ _ J
          (restriction positiveG A B J c d n m K)
    simp only [map_add]
  map_smul' a I := by
    funext c d
    apply LinearMap.ext
    intro n
    apply LinearMap.ext
    intro m
    change Sectors.ActualWeakTargetFullFusion.inverseLinear positiveG _ _ J
      (restriction positiveG A B J c d n m (a • I)) =
        a • Sectors.ActualWeakTargetFullFusion.inverseLinear positiveG _ _ J
          (restriction positiveG A B J c d n m I)
    simp only [map_smul]

/-- Reconstruction as an equality of COMPLETE lawful Hahn fields, using
the original sector forward_inverse with its original hypotheses intact. -/
theorem sector_forward_extraction (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) (I : FullFields positiveG A B J)
    (c d : Discriminant D) (n : Multiplicity A c) (m : Multiplicity B d) :
    Sectors.ActualWeakTargetFullFusion.forward positiveG (representative D c) (representative D d) J
      (extractionLinear positiveG A B J I c d n m) =
        restriction positiveG A B J c d n m I :=
  Sectors.ActualWeakTargetFullFusion.forward_inverse positiveG (representative D c) (representative D d) J _

/-- Literal equality in Z at every original Hahn exponent, with exactly
the original B=id charged canonical field and normalization. -/
theorem reconstruction_coeff (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) (I : FullFields positiveG A B J)
    (c d : Discriminant D) (n : Multiplicity A c) (m : Multiplicity B d)
    (s t : Carrier D) (q : ℚ) :
    (extractionLinear positiveG A B J I c d n m).val
      ((LatticeCosetCanonicalIntertwiner.intertwiner D (1 : Matrix _ _ ℤ)
        (representative D c) (representative D d) s).coeff q t) =
      (I.val ((inclusionLinear positiveG A c n).val s)).coeff q
        ((inclusionLinear positiveG B d m).val t) := by
  have he := congrArg (fun F : Sectors.ActualWeakTargetFullFusion.FullFields positiveG
    (representative D c) (representative D d) J => (F.val s).coeff q t)
      (sector_forward_extraction positiveG A B J I c d n m)
  simpa only [Sectors.ActualWeakTargetFullFusion.forward_coefficient, Sectors.ActualWeakTargetFullFusion.canonical_val, restriction_coeff] using he

/-- The entire extraction is faithful on arbitrary original full fields.
Theta-inverse finite support and TWO tensor/direct-sum inductions extend
the reconstructed sector coefficients to every x:X and y:Y. -/
theorem extractionLinear_injective (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) :
    Function.Injective (extractionLinear positiveG A B J) := by
  intro I K hIK
  have he (c d : Discriminant D) (n : Multiplicity A c) (m : Multiplicity B d)
      (s t : Carrier D) (q : ℚ) :
      (I.val ((inclusionLinear positiveG A c n).val s)).coeff q
          ((inclusionLinear positiveG B d m).val t) =
        (K.val ((inclusionLinear positiveG A c n).val s)).coeff q
          ((inclusionLinear positiveG B d m).val t) := by
    rw [← reconstruction_coeff positiveG A B J I c d n m s t q,
      ← reconstruction_coeff positiveG A B J K c d n m s t q, hIK]
  have hi (c : Discriminant D) (n : Multiplicity A c) (s : Carrier D)
      (y : Y) (q : ℚ) :
      (I.val ((inclusionLinear positiveG A c n).val s)).coeff q y =
        (K.val ((inclusionLinear positiveG A c n).val s)).coeff q y := by
    apply induction_on_inclusions positiveG B y
      (fun y => (I.val ((inclusionLinear positiveG A c n).val s)).coeff q y =
        (K.val ((inclusionLinear positiveG A c n).val s)).coeff q y)
    · simp only [map_zero]
    · intro y y' hy hy'
      simp only [map_add, hy, hy']
    · intro d m t
      exact he c d n m s t q
  apply Subtype.ext
  apply ActualWeakModuleFullIntertwiner.fields_ext
  intro x y q
  apply induction_on_inclusions positiveG A x
    (fun x => (I.val x).coeff q y = (K.val x).coeff q y)
  · simp
  · intro x x' hx hx'
    simp only [map_add, Pi.add_apply, LinearMap.add_apply, hx, hx']
  · intro c n s
    exact hi c n s y q

section Naturality
variable {X' : Type uX'} {Y' : Type uY'} {Z' : Type uZ'}
variable [AddCommGroup X'] [Module ℂ X'] [AddCommGroup Y'] [Module ℂ Y']
variable [AddCommGroup Z'] [Module ℂ Z']

/-- Naturality of the actual inclusion, derived from the PUBLIC Hom
correspondence's left inverse. No private supplier lemma is named. -/
theorem inclusion_natural (positiveG : (gramReal D).PosDef)
    {A : FullJacobiLatticeModule D X} {A' : FullJacobiLatticeModule D X'}
    (f : ModuleHom A' A) (c : Discriminant D) (n : Multiplicity A' c) (s : Carrier D) :
    f.linearMap ((inclusionLinear positiveG A' c n).val s) =
      (inclusionLinear positiveG A c (ActualWeakModuleHom.restrict f c n)).val s := by
  have hf := (ActualWeakModuleHom.homMultiplicityEquiv A' A positiveG).symm_apply_apply
    (recordEquiv A' A f)
  have hv := congrArg (fun k : homSpace A' A =>
    k.val ((inclusionLinear positiveG A' c n).val s)) hf
  change classificationEquiv A positiveG
    (DirectSum.lmap (fun e => TensorProduct.map LinearMap.id
      (ActualWeakModuleHom.restrict f e))
      ((classificationEquiv A' positiveG).symm
        (classificationEquiv A' positiveG
          (DirectSum.lof ℂ (Discriminant D) (Sector A') c (s ⊗ₜ[ℂ] n))))) = _ at hv
  rw [(classificationEquiv A' positiveG).symm_apply_apply,
    DirectSum.lmap_lof, TensorProduct.map_tmul, LinearMap.id_apply] at hv
  exact hv.symm

theorem restriction_natural (positiveG : (gramReal D).PosDef)
    {A : FullJacobiLatticeModule D X} {B : FullJacobiLatticeModule D Y}
    {J : FullJacobiLatticeModule D Z}
    {A' : FullJacobiLatticeModule D X'} {B' : FullJacobiLatticeModule D Y'}
    {J' : FullJacobiLatticeModule D Z'}
    (f : ModuleHom A' A) (g : ModuleHom B' B) (k : ModuleHom J J')
    (I : FullFields positiveG A B J) (c d : Discriminant D)
    (n : Multiplicity A' c) (m : Multiplicity B' d) :
    restriction positiveG A' B' J' c d n m
        (ActualWeakModuleFullIntertwiner.map (inverseGram positiveG) f g k I) =
      Sectors.ActualWeakTargetFullIntertwiner.post (representative D c) (representative D d) (inverseGram positiveG) k
        (restriction positiveG A B J c d
          (ActualWeakModuleHom.restrict f c n) (ActualWeakModuleHom.restrict g d m) I) := by
  apply Subtype.ext
  apply Sectors.ActualWeakTargetFullIntertwiner.fields_ext
  intro s t q
  rw [restriction_coeff, ActualWeakModuleFullIntertwiner.map_coeff, inclusion_natural, inclusion_natural,
    Sectors.ActualWeakTargetFullIntertwiner.post_coeff, restriction_coeff]

/-- Simultaneous contravariance in both original inputs and covariance in
the original target. All maps may be zero or noninjective, in independent
universes. The input maps on multiplicities are the actual Hom restrictions. -/
theorem extraction_natural (positiveG : (gramReal D).PosDef)
    {A : FullJacobiLatticeModule D X} {B : FullJacobiLatticeModule D Y}
    {J : FullJacobiLatticeModule D Z}
    {A' : FullJacobiLatticeModule D X'} {B' : FullJacobiLatticeModule D Y'}
    {J' : FullJacobiLatticeModule D Z'}
    (f : ModuleHom A' A) (g : ModuleHom B' B) (k : ModuleHom J J')
    (I : FullFields positiveG A B J) (c d : Discriminant D)
    (n : Multiplicity A' c) (m : Multiplicity B' d) :
    extractionLinear positiveG A' B' J'
        (ActualWeakModuleFullIntertwiner.map (inverseGram positiveG) f g k I) c d n m =
      Sectors.ActualWeakTargetFullFusion.targetHomMap (representative D c) (representative D d) J k
        (extractionLinear positiveG A B J I c d
          (ActualWeakModuleHom.restrict f c n) (ActualWeakModuleHom.restrict g d m)) := by
  change Sectors.ActualWeakTargetFullFusion.inverse positiveG (representative D c) (representative D d) J'
    (restriction positiveG A' B' J' c d n m
      (ActualWeakModuleFullIntertwiner.map (inverseGram positiveG) f g k I)) = _
  rw [restriction_natural]
  exact Sectors.ActualWeakTargetFullFusion.inverse_natural positiveG (representative D c) (representative D d) J k _

end Naturality

end D5.S3.VertexAlgebra.Modules.ActualWeakModuleIntertwinerExtraction
