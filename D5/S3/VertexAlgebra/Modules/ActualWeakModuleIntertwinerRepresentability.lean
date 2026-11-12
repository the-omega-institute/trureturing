/-
SOURCE_ONLY_UNCOMPILED_UNACCEPTED.  No native compiler, build, report, judge,
new Pro request, worktree, clone, donor, or live-worker artifact was used here.

Repair of source 86d9a4aa5791c5a33c0ac1a4fef15cc94137591270292a9b7e4e34dc64666fe6:
its old mathematical completion claim is rejected.  FullFields now uses the
arbitrary ORIGINAL target J; universalElement still has the exact target P(A,B).

This file is the actual arbitrary-original-input representability layer.  It
consumes the three exact terminal source pins recorded by the parent intake:
ActualWeakModuleFullIntertwiner, ActualWeakModuleIntertwinerExtraction, and
ActualWeakModuleUniversalField.  The sector fusion API is the original
67-header source API and remains native-pending elsewhere.  All claims below
therefore remain conditional on the caller's future native checks.

The representing module is the literal dependent direct sum P and its literal
FullJacobiDirectSum/tensorModule action; represented fields have arbitrary J.
The only positivity premise is the
original positiveG used by classification and sector fusion.  No basis,
finite-dimensionality, nonzero carrier, decomposition, or uniform support
premise is introduced.  TensorProduct.lift is used before the dependent
coproductHom.  All coefficient statements quantify over the original states,
all integer modes, and all rational exponents.
-/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleUniversalField
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleIntertwinerExtraction
import D5.S3.VertexAlgebra.Sectors.ActualWeakTargetFullFusion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleIntertwinerRepresentability

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeDiscriminantTheta LatticeDualCosetModule LatticeDualCosetConformal
open FullJacobiCurrentTransport FullJacobiIntertwiner
open FullJacobiTensorModule FullJacobiDirectSum
open ActualWeakModuleSectorCoordinates ActualWeakModuleClassification
open ActualWeakModuleScalarProbes (sectorModule sectorModule_mode)
open ActualWeakModuleHom (homSpace recordEquiv)
open ActualWeakModuleUniversalField
open ActualWeakModuleIntertwinerExtraction

universe uX uY uZ uX' uY' uZ' uX'' uY'' uZ''

variable {D : LatticeData}
variable {X : Type uX} {Y : Type uY} {Z : Type uZ}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable [AddCommGroup Z] [Module ℂ Z]
attribute [local instance] Classical.propDecidable

abbrev H (positiveG : (gramReal D).PosDef) : Matrix (Fin D.rank) (Fin D.rank) ℂ :=
  inverseGram positiveG

abbrev FullFields (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) :=
  ActualWeakModuleFullIntertwiner.operatorSpace A B
    J (H positiveG)

/-- The universal field is an element of the exact generic lawful operator
space.  Every clause is the corresponding original U theorem, after unfolding
only the generic coefficient/mode and the literal omega-zero translation. -/
def universalElement (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y) :
    ActualWeakModuleFullIntertwiner.operatorSpace A B
      (ActualWeakModuleUniversalField.targetModule A B) (H positiveG) := by
  refine ⟨ActualWeakModuleUniversalField.U A B positiveG, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x τ
    apply LinearMap.ext
    intro y
    simpa only [ActualWeakModuleFullIntertwiner.mode,
      ActualWeakModuleUniversalField.translation,
      Sectors.ActualWeakTargetFullIntertwiner.targetTranslation,
      LinearMap.smul_apply] using
      ActualWeakModuleUniversalField.U_source_translation A B positiveG x y τ
  · intro x τ
    apply LinearMap.ext
    intro y
    simpa only [ActualWeakModuleFullIntertwiner.mode,
      ActualWeakModuleUniversalField.translation,
      Sectors.ActualWeakTargetFullIntertwiner.targetTranslation,
      LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply] using
      ActualWeakModuleUniversalField.U_target_translation A B positiveG x y τ
  · intro h x y p r τ
    refine ⟨?_, ?_, ?_, ?_⟩
    · change Function.HasFiniteSupport
        (ActualWeakModuleUniversalField.leftTerm A B positiveG h x y p r τ)
      exact ActualWeakModuleUniversalField.U_left_finite A B positiveG h x y p r τ
    · change Function.HasFiniteSupport
        (ActualWeakModuleUniversalField.firstTerm A B positiveG h x y p r τ)
      exact ActualWeakModuleUniversalField.U_first_finite A B positiveG h x y p r τ
    · change Function.HasFiniteSupport
        (ActualWeakModuleUniversalField.secondTerm A B positiveG h x y p r τ)
      exact ActualWeakModuleUniversalField.U_second_finite A B positiveG h x y p r τ
    · simpa only [ActualWeakModuleFullIntertwiner.leftTerm,
        ActualWeakModuleFullIntertwiner.firstTerm,
        ActualWeakModuleFullIntertwiner.secondTerm,
        ActualWeakModuleFullIntertwiner.mode,
        ActualWeakModuleUniversalField.leftTerm,
        ActualWeakModuleUniversalField.firstTerm,
        ActualWeakModuleUniversalField.secondTerm, FullJacobiCurrentTransport.mode] using
        ActualWeakModuleUniversalField.U_mixed_jacobi A B positiveG h x y p r τ

@[simp] theorem universalElement_coeff (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (x : X) (y : Y) (q : ℚ) :
    ((universalElement positiveG A B).val x).coeff q y =
      (ActualWeakModuleUniversalField.U A B positiveG x).coeff q y := rfl

/-- The balanced coefficient map for one pair of classification sectors.  The
outer lift is the carrier factor; the inner lift is the two multiplicity
factors.  Thus the ordinary tensor balancing is completed before the dependent
external direct sum is assembled. -/
def pairLinear (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z)
    (I : FullFields positiveG A B J) (c d : Discriminant D) :
    Carrier D ⊗[ℂ]
        (Multiplicity A c ⊗[ℂ] Multiplicity B d) →ₗ[ℂ] Z :=
  TensorProduct.lift
    { toFun := fun x =>
        TensorProduct.lift
          { toFun := fun n =>
              { toFun := fun m =>
                  (extractionLinear positiveG A B J I c d n m).val x
                map_add' := by
                  intro m m'
                  change (extractionLinear positiveG A B J I c d n (m + m')).val x = _
                  simp only [map_add, Submodule.coe_add, LinearMap.add_apply,
                    TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk] <;> rfl
                map_smul' := by
                  intro a m
                  change (extractionLinear positiveG A B J I c d n (a • m)).val x = _
                  simp only [map_smul, Submodule.coe_smul, LinearMap.smul_apply, RingHom.id_apply,
                    TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk] <;> rfl }
            map_add' := by
              intro n n'
              apply LinearMap.ext
              intro m
              change (extractionLinear positiveG A B J I c d (n + n') m).val x = _
              simp only [map_add, Submodule.coe_add, LinearMap.add_apply,
                    TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk] <;> rfl
            map_smul' := by
              intro a n
              apply LinearMap.ext
              intro m
              change (extractionLinear positiveG A B J I c d (a • n) m).val x = _
              simp only [map_smul, Submodule.coe_smul, LinearMap.smul_apply, RingHom.id_apply,
                    TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk] <;> rfl }
      map_add' := by
        intro x x'
        apply TensorProduct.ext'
        intro n m
        change (extractionLinear positiveG A B J I c d n m).val (x + x') = _
        simp only [map_add, Submodule.coe_add, LinearMap.add_apply,
                    TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk] <;> rfl
      map_smul' := by
        intro a x
        apply TensorProduct.ext'
        intro n m
        change (extractionLinear positiveG A B J I c d n m).val (a • x) = _
        simp only [map_smul, Submodule.coe_smul, LinearMap.smul_apply, RingHom.id_apply,
                    TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk] <;> rfl }

@[simp] theorem pairLinear_tmul (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) (I : FullFields positiveG A B J)
    (c d : Discriminant D) (x : Carrier D)
    (n : Multiplicity A c) (m : Multiplicity B d) :
    pairLinear positiveG A B J I c d (x ⊗ₜ[ℂ] (n ⊗ₜ[ℂ] m)) =
      (extractionLinear positiveG A B J I c d n m).val x := by
  rfl

/-- A sector-pair map is a genuine ModuleHom.  The intertwining proof is by
the zero/tensor/add TensorProduct.induction_on in both tensor layers and uses the original
all-state/all-integer-mode law of each extracted sector Hom. -/
def pairHom (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) (I : FullFields positiveG A B J)
    (c d : Discriminant D) :
    ModuleHom
      (tensorModule (sectorModule D (representative D c + representative D d))
        (Multiplicity A c ⊗[ℂ] Multiplicity B d)) J where
  linearMap := pairLinear positiveG A B J I c d
  intertwines := by
    intro h k z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x w =>
        induction w using TensorProduct.induction_on with
        | zero => simp
        | tmul n m =>
            simp only [tensorModule_mode, TensorProduct.map_tmul,
              LinearMap.id_apply, pairLinear_tmul]
            simpa only [sectorModule_mode,
              Sectors.ActualWeakTargetFullIntertwiner.scalarModule,
              FullJacobiCurrentTransport.mode] using
              (extractionLinear positiveG A B J I c d n m).property h k x
        | add w w' hw hw' =>
            simpa only [TensorProduct.tmul_add, map_add, hw, hw']
    | add z z' hz hz' => simpa only [map_add, hz, hz']

/-- The direct-sum coproduct supplied by FullJacobiDirectSum. -/
def backwardHom (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) (I : FullFields positiveG A B J) :
    ModuleHom (ActualWeakModuleUniversalField.targetModule A B) J := by
  simpa only [ActualWeakModuleUniversalField.targetModule] using
    (FullJacobiDirectSum.coproductHom
      (fun cd : Discriminant D × Discriminant D =>
        tensorModule (sectorModule D (representative D cd.1 + representative D cd.2))
          (Multiplicity A cd.1 ⊗[ℂ] Multiplicity B cd.2)) J
      (fun cd => pairHom positiveG A B J I cd.1 cd.2))

@[simp] theorem backwardHom_elementary (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) (I : FullFields positiveG A B J)
    (c d : Discriminant D) (x : Carrier D)
    (n : Multiplicity A c) (m : Multiplicity B d) :
    (backwardHom positiveG A B J I).linearMap
      (DirectSum.lof ℂ (Discriminant D × Discriminant D)
        (fun cd => ActualWeakModuleUniversalField.PairSector A B cd) (c,d)
        (x ⊗ₜ[ℂ] (n ⊗ₜ[ℂ] m))) =
      (extractionLinear positiveG A B J I c d n m).val x := by
  change DirectSum.toModule ℂ (Discriminant D × Discriminant D) Z
      (fun cd => (pairHom positiveG A B J I cd.1 cd.2).linearMap)
      (DirectSum.lof ℂ (Discriminant D × Discriminant D)
        (fun cd => ActualWeakModuleUniversalField.PairSector A B cd) (c,d)
        (x ⊗ₜ[ℂ] (n ⊗ₜ[ℂ] m))) = _
  rw [DirectSum.toModule_lof]
  change pairLinear positiveG A B J I c d (x ⊗ₜ[ℂ] (n ⊗ₜ[ℂ] m)) = _
  exact pairLinear_tmul positiveG A B J I c d x n m

/-- Equality on every algebraic tensor generator determines a linear map on
the entire original dependent direct sum, including its zero summands. -/
private theorem linearMap_ext_elementary
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    {f g : ActualWeakModuleUniversalField.P A B →ₗ[ℂ] Z}
    (h : ∀ (c d : Discriminant D) (x : Carrier D)
      (n : Multiplicity A c) (m : Multiplicity B d),
      f (DirectSum.lof ℂ _ (ActualWeakModuleUniversalField.PairSector A B) (c,d)
        (x ⊗ₜ[ℂ] (n ⊗ₜ[ℂ] m))) =
      g (DirectSum.lof ℂ _ (ActualWeakModuleUniversalField.PairSector A B) (c,d)
        (x ⊗ₜ[ℂ] (n ⊗ₜ[ℂ] m)))) : f = g := by
  apply DirectSum.linearMap_ext
  intro cd
  apply TensorProduct.ext'
  intro x w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul n m => exact h cd.1 cd.2 x n m
  | add w w' hw hw' =>
      simpa only [LinearMap.comp_apply, TensorProduct.tmul_add, map_add] using
        congrArg₂ (· + ·) hw hw'

/-- The backward map is linear in the complete lawful field.  Extensionality
uses exactly the direct-sum and algebraic-tensor generators, with no basis or
decomposition choice. -/
def backward (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) :
    FullFields positiveG A B J →ₗ[ℂ]
      homSpace (ActualWeakModuleUniversalField.targetModule A B) J where
  toFun I := recordEquiv (ActualWeakModuleUniversalField.targetModule A B) J
    (backwardHom positiveG A B J I)
  map_add' I K := by
    apply Subtype.ext
    apply linearMap_ext_elementary A B
    intro c d x n m
    change (backwardHom positiveG A B J (I + K)).linearMap _ =
      (backwardHom positiveG A B J I).linearMap _ +
        (backwardHom positiveG A B J K).linearMap _
    rw [backwardHom_elementary, backwardHom_elementary, backwardHom_elementary]
    exact congrArg (fun F : ∀ c d : Discriminant D,
        Multiplicity A c →ₗ[ℂ] Multiplicity B d →ₗ[ℂ]
          Sectors.ActualWeakTargetFullFusion.Hom (representative D c + representative D d) J =>
        (F c d n m).val x)
      ((extractionLinear positiveG A B J).map_add I K)
  map_smul' a I := by
    apply Subtype.ext
    apply linearMap_ext_elementary A B
    intro c d x n m
    change (backwardHom positiveG A B J (a • I)).linearMap _ =
      a • (backwardHom positiveG A B J I).linearMap _
    rw [backwardHom_elementary, backwardHom_elementary]
    exact congrArg (fun F : ∀ c d : Discriminant D,
        Multiplicity A c →ₗ[ℂ] Multiplicity B d →ₗ[ℂ]
          Sectors.ActualWeakTargetFullFusion.Hom (representative D c + representative D d) J =>
        (F c d n m).val x)
      ((extractionLinear positiveG A B J).map_smul a I)

/-- The forward map is postcomposition of the very same lawful universal U. -/
def forward (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) :
    homSpace (ActualWeakModuleUniversalField.targetModule A B) J →ₗ[ℂ]
      FullFields positiveG A B J where
  toFun f :=
    ActualWeakModuleFullIntertwiner.post A B (H positiveG)
      ((recordEquiv (ActualWeakModuleUniversalField.targetModule A B) J).symm f)
      (universalElement positiveG A B)
  map_add' f g := by
    simpa only [ActualWeakModuleFullIntertwiner.postLinear,LinearMap.coe_mk,
      AddHom.coe_mk,LinearMap.add_apply] using
      congrArg (fun T => T (universalElement positiveG A B))
        ((ActualWeakModuleFullIntertwiner.postLinear
          (A := A) (B := B) (J := targetModule A B) (J' := J)
          (H positiveG)).map_add f g)
  map_smul' a f := by
    simpa only [ActualWeakModuleFullIntertwiner.postLinear,LinearMap.coe_mk,
      AddHom.coe_mk,LinearMap.smul_apply, RingHom.id_apply] using
      congrArg (fun T => T (universalElement positiveG A B))
        ((ActualWeakModuleFullIntertwiner.postLinear
          (A := A) (B := B) (J := targetModule A B) (J' := J)
          (H positiveG)).map_smul a f)

@[simp] theorem forward_coeff (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z)
    (f : homSpace (ActualWeakModuleUniversalField.targetModule A B) J)
    (x : X) (y : Y) (q : ℚ) :
    ((forward positiveG A B J f).val x).coeff q y =
      f.val ((ActualWeakModuleUniversalField.U A B positiveG x).coeff q y) := by
  exact ActualWeakModuleFullIntertwiner.map_coeff (H positiveG)
    (ModuleHom.id A) (ModuleHom.id B)
    ((recordEquiv (ActualWeakModuleUniversalField.targetModule A B) J).symm f)
    (universalElement positiveG A B) x y q

/-- The elementary coefficient equation for the backward map. -/
theorem backward_coeff_elementary (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) (I : FullFields positiveG A B J)
    (c d : Discriminant D) (x y : Carrier D)
    (n : Multiplicity A c) (m : Multiplicity B d) (q : ℚ) :
    (backward positiveG A B J I).val
      (DirectSum.lof ℂ (Discriminant D × Discriminant D)
        (fun cd => ActualWeakModuleUniversalField.PairSector A B cd) (c,d)
        (x ⊗ₜ[ℂ] (n ⊗ₜ[ℂ] m))) =
      (extractionLinear positiveG A B J I c d n m).val x := by
  exact backwardHom_elementary positiveG A B J I c d x n m

/-- Forward after backward agrees with the original field at every rational
coefficient.  The first equality is the supplied sector reconstruction on the
classification inclusions; the two induction_on_inclusions calls then cover
all original X and Y vectors. -/
theorem forward_backward (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) (I : FullFields positiveG A B J) :
    forward positiveG A B J (backward positiveG A B J I) = I := by
  apply Subtype.ext
  apply ActualWeakModuleFullIntertwiner.fields_ext
  intro x y q
  apply induction_on_inclusions positiveG A x
    (fun x => ((forward positiveG A B J (backward positiveG A B J I)).val x).coeff q y =
      (I.val x).coeff q y)
  · simp
  · intro x x' hx hx'
    simpa only [map_add, Pi.add_apply, LinearMap.add_apply] using congrArg₂ (· + ·) hx hx'
  · intro c n s
    apply induction_on_inclusions positiveG B y
      (fun y => ((forward positiveG A B J (backward positiveG A B J I)).val
          ((inclusionLinear positiveG A c n).val s)).coeff q y =
        (I.val ((inclusionLinear positiveG A c n).val s)).coeff q y)
    · simp
    · intro y y' hy hy'
      simpa only [map_add, Pi.add_apply, LinearMap.add_apply] using congrArg₂ (· + ·) hy hy'
    · intro d m t
      rw [forward_coeff]
      change (backward positiveG A B J I).val
        ((ActualWeakModuleUniversalField.U A B positiveG
          (classificationEquiv A positiveG
            (ActualWeakModuleUniversalField.elementary A c s n))).coeff q
          (classificationEquiv B positiveG
            (ActualWeakModuleUniversalField.elementary B d t m))) = _
      rw [ActualWeakModuleUniversalField.U_elementary_coeff]
      change (backwardHom positiveG A B J I).linearMap _ = _
      rw [backwardHom_elementary]
      exact reconstruction_coeff positiveG A B J I c d n m s t q

/-- The canonical source/input inclusion into P, used for the reverse inverse
law. -/
def pairInclusionHom (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (c d : Discriminant D) (n : Multiplicity A c) (m : Multiplicity B d) :
    ModuleHom (sectorModule D (representative D c + representative D d))
      (ActualWeakModuleUniversalField.targetModule A B) :=
  ActualWeakModuleUniversalField.tagHom A B c d n m

/-- The extracted sector map for the forward field is the literal component of
f along the same pairInclusionHom.  Equality is established by the original
sector forward inverse/injectivity, never by a coordinate projection. -/
def componentHom (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z)
    (f : homSpace (ActualWeakModuleUniversalField.targetModule A B) J)
    (c d : Discriminant D) (n : Multiplicity A c) (m : Multiplicity B d) :
    Sectors.ActualWeakTargetFullFusion.Hom
      (representative D c + representative D d) J := by
  refine ⟨f.val.comp (ActualWeakModuleUniversalField.tag A B c d n m), ?_⟩
  intro h r v
  change f.val (ActualWeakModuleUniversalField.tag A B c d n m
      (((action D (representative D c + representative D d) h)[[r]]) v)) =
    mode J h r (f.val (ActualWeakModuleUniversalField.tag A B c d n m v))
  rw [← ActualWeakModuleUniversalField.target_action_tag A B c d n m h v r]
  exact f.property h r _

/-- The sector field used by componentHom is exactly the restriction of the
forward field.  This is a coefficientwise equality of complete Hahn fields. -/
theorem component_forward_restriction (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z)
    (f : homSpace (ActualWeakModuleUniversalField.targetModule A B) J)
    (c d : Discriminant D) (n : Multiplicity A c) (m : Multiplicity B d) :
    Sectors.ActualWeakTargetFullFusion.forward positiveG
        (representative D c) (representative D d) J
        (componentHom positiveG A B J f c d n m) =
      restriction positiveG A B J c d n m
        (forward positiveG A B J f) := by
  apply Subtype.ext
  apply Sectors.ActualWeakTargetFullIntertwiner.fields_ext
  intro s t q
  simp only [Sectors.ActualWeakTargetFullFusion.forward_coefficient,
    Sectors.ActualWeakTargetFullFusion.canonical_val,
    restriction_coeff, forward_coeff, inclusion_apply,
    ActualWeakModuleUniversalField.U_elementary_coeff]
  simp only [componentHom, LinearMap.comp_apply,
    ActualWeakModuleUniversalField.tag_apply, C]

/-- Backward after forward is equality on every direct-sum/tensor generator;
the sector inverse_forward and the supplied sector forward injectivity identify
its extracted map with componentHom. -/
theorem backward_forward (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z)
    (f : homSpace (ActualWeakModuleUniversalField.targetModule A B) J) :
    (backward positiveG A B J (forward positiveG A B J f)).val = f.val := by
  apply linearMap_ext_elementary A B
  intro c d x n m
  have hsector :=
    (Sectors.ActualWeakTargetFullFusion.forward_injective positiveG
      (representative D c) (representative D d) J)
  have heq := component_forward_restriction positiveG A B J f c d n m
  have hex := sector_forward_extraction positiveG A B J
      (forward positiveG A B J f) c d n m
  have hcomp : extractionLinear positiveG A B J
      (forward positiveG A B J f) c d n m =
        componentHom positiveG A B J f c d n m := by
    apply hsector
    rw [hex, heq]
  change (backwardHom positiveG A B J (forward positiveG A B J f)).linearMap _ = _
  rw [backwardHom_elementary]
  rw [hcomp]
  simp only [componentHom, LinearMap.comp_apply,
    ActualWeakModuleUniversalField.tag_apply]

/- The forward LinearMap is injective by the already established reverse
   equation; no injectivity field of LinearMap is assumed. -/
theorem forward_injective (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) :
    Function.Injective (forward positiveG A B J) := by
  intro f g h
  apply Subtype.ext
  calc
    f.val = (backward positiveG A B J (forward positiveG A B J f)).val :=
      (backward_forward positiveG A B J f).symm
    _ = (backward positiveG A B J (forward positiveG A B J g)).val :=
      congrArg (fun I => (backward positiveG A B J I).val) h
    _ = g.val := backward_forward positiveG A B J g

/-- The desired complex-linear equivalence. -/
def equivalence (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) :
    homSpace (ActualWeakModuleUniversalField.targetModule A B) J ≃ₗ[ℂ]
      FullFields positiveG A B J where
  toLinearMap := forward positiveG A B J
  invFun := backward positiveG A B J
  left_inv f := by
    apply Subtype.ext
    exact backward_forward positiveG A B J f
  right_inv I := forward_backward positiveG A B J I

@[simp] theorem equivalence_forward (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z)
    (f : homSpace (ActualWeakModuleUniversalField.targetModule A B) J) :
    equivalence positiveG A B J f = forward positiveG A B J f := rfl

@[simp] theorem equivalence_symm (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z)
    (I : FullFields positiveG A B J) :
    (equivalence positiveG A B J).symm I = backward positiveG A B J I := rfl

/-- The literal coefficient characterization of every represented field, at
all original inputs and rational exponents. -/
theorem equivalence_coefficient (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z)
    (f : homSpace (ActualWeakModuleUniversalField.targetModule A B) J)
    (x : X) (y : Y) (q : ℚ) :
    ((equivalence positiveG A B J f).val x).coeff q y =
      f.val ((ActualWeakModuleUniversalField.U A B positiveG x).coeff q y) := by
  exact forward_coeff positiveG A B J f x y q

/- The target-side hom map is record composition transported through the
   faithful homSpace/ModuleHom correspondence. -/
def targetHomMap
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    {Z' : Type uZ'} [AddCommGroup Z'] [Module ℂ Z']
    {J : FullJacobiLatticeModule D Z} {J' : FullJacobiLatticeModule D Z'}
    (k : ModuleHom J J') :
    homSpace (ActualWeakModuleUniversalField.targetModule A B) J →ₗ[ℂ]
      homSpace (ActualWeakModuleUniversalField.targetModule A B) J' where
  toFun f := recordEquiv (ActualWeakModuleUniversalField.targetModule A B) J'
    (k.comp ((recordEquiv (ActualWeakModuleUniversalField.targetModule A B) J).symm f))
  map_add' f g := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change k.linearMap (f.val x + g.val x) = k.linearMap (f.val x) + k.linearMap (g.val x)
    exact k.linearMap.map_add _ _
  map_smul' a f := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change k.linearMap (a • f.val x) = a • k.linearMap (f.val x)
    exact k.linearMap.map_smul a _

theorem targetHomMap_id
    (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) :
    targetHomMap A B (ModuleHom.id J) = LinearMap.id := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  rfl

theorem targetHomMap_comp
    {Z' : Type uZ'} [AddCommGroup Z'] [Module ℂ Z']
    {Z'' : Type uZ''} [AddCommGroup Z''] [Module ℂ Z'']
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    {J : FullJacobiLatticeModule D Z} {J' : FullJacobiLatticeModule D Z'}
    {J'' : FullJacobiLatticeModule D Z''}
    (k : ModuleHom J J') (k' : ModuleHom J' J'') :
    targetHomMap A B (k'.comp k) =
      (targetHomMap A B k').comp (targetHomMap A B k) := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  rfl

/-- Target postcomposition, including zero and noninjective maps. -/
theorem forward_target_natural
    {Z' : Type uZ'} [AddCommGroup Z'] [Module ℂ Z']
    (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) (J' : FullJacobiLatticeModule D Z')
    (k : ModuleHom J J')
    (f : homSpace (ActualWeakModuleUniversalField.targetModule A B) J) :
    forward positiveG A B J' (targetHomMap A B k f) =
      ActualWeakModuleFullIntertwiner.post A B (H positiveG) k
        (forward positiveG A B J f) := by
  apply Subtype.ext
  apply ActualWeakModuleFullIntertwiner.fields_ext
  intro x y q
  simp only [forward_coeff, ActualWeakModuleFullIntertwiner.post,
    ActualWeakModuleFullIntertwiner.map_coeff, ModuleHom.id, LinearMap.id_apply]
  rfl

/-- Naturality of the representing equivalence in the target slot, obtained by
uniqueness through the forward inverse law. -/
theorem equivalence_target_natural
    {Z' : Type uZ'} [AddCommGroup Z'] [Module ℂ Z']
    (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) (J' : FullJacobiLatticeModule D Z')
    (k : ModuleHom J J') (I : FullFields positiveG A B J) :
    (equivalence positiveG A B J').symm
      (ActualWeakModuleFullIntertwiner.post A B (H positiveG) k I) =
      targetHomMap A B k ((equivalence positiveG A B J).symm I) := by
  apply forward_injective positiveG A B J'
  rw [equivalence_symm, equivalence_symm, forward_backward,
    forward_target_natural, forward_backward]

/-- The actual bifunctor input map P(A',B') -> P(A) is obtained by applying
backward to restriction of the actual universal U. -/
def inputMap
    {X' : Type uX'} {Y' : Type uY'}
    [AddCommGroup X'] [Module ℂ X'] [AddCommGroup Y'] [Module ℂ Y']
    (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (A' : FullJacobiLatticeModule D X') (B' : FullJacobiLatticeModule D Y')
    (f : ModuleHom A' A) (g : ModuleHom B' B) :
    homSpace (ActualWeakModuleUniversalField.targetModule A' B')
      (ActualWeakModuleUniversalField.targetModule A B) :=
  backward positiveG A' B' (ActualWeakModuleUniversalField.targetModule A B)
    (ActualWeakModuleFullIntertwiner.map (H positiveG) f g
      (ModuleHom.id (ActualWeakModuleUniversalField.targetModule A B))
      (universalElement positiveG A B))

@[simp] theorem inputMap_field_preserving
    {X' : Type uX'} {Y' : Type uY'}
    [AddCommGroup X'] [Module ℂ X'] [AddCommGroup Y'] [Module ℂ Y']
    (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (A' : FullJacobiLatticeModule D X') (B' : FullJacobiLatticeModule D Y')
    (f : ModuleHom A' A) (g : ModuleHom B' B) :
    forward positiveG A' B' (ActualWeakModuleUniversalField.targetModule A B)
      (inputMap positiveG A B A' B' f g) =
      ActualWeakModuleFullIntertwiner.map (H positiveG) f g
        (ModuleHom.id (ActualWeakModuleUniversalField.targetModule A B))
        (universalElement positiveG A B) := by
  exact forward_backward positiveG A' B' (ActualWeakModuleUniversalField.targetModule A B) _

/-- Identity and composition of the actual input maps. -/
theorem inputMap_id
    {X' : Type uX'} {Y' : Type uY'}
    [AddCommGroup X'] [Module ℂ X'] [AddCommGroup Y'] [Module ℂ Y']
    (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X') (B : FullJacobiLatticeModule D Y') :
    inputMap positiveG A B A B (ModuleHom.id A) (ModuleHom.id B) =
      recordEquiv (ActualWeakModuleUniversalField.targetModule A B)
        (ActualWeakModuleUniversalField.targetModule A B)
        (ModuleHom.id (ActualWeakModuleUniversalField.targetModule A B)) := by
  apply forward_injective positiveG A B (ActualWeakModuleUniversalField.targetModule A B)
  calc
    forward positiveG A B (ActualWeakModuleUniversalField.targetModule A B)
        (inputMap positiveG A B A B (ModuleHom.id A) (ModuleHom.id B)) =
      ActualWeakModuleFullIntertwiner.map (H positiveG) (ModuleHom.id A)
        (ModuleHom.id B) (ModuleHom.id (ActualWeakModuleUniversalField.targetModule A B))
        (universalElement positiveG A B) :=
      inputMap_field_preserving positiveG A B A B (ModuleHom.id A) (ModuleHom.id B)
    _ = universalElement positiveG A B :=
      congrArg (fun T => T (universalElement positiveG A B))
        (ActualWeakModuleFullIntertwiner.map_id (A := A) (B := B)
          (J := ActualWeakModuleUniversalField.targetModule A B) (H positiveG))
    _ = forward positiveG A B (ActualWeakModuleUniversalField.targetModule A B)
        (recordEquiv (ActualWeakModuleUniversalField.targetModule A B)
          (ActualWeakModuleUniversalField.targetModule A B)
          (ModuleHom.id (ActualWeakModuleUniversalField.targetModule A B))) := by
      apply Subtype.ext
      apply ActualWeakModuleFullIntertwiner.fields_ext
      intro x y q
      simp only [forward_coeff, recordEquiv, ModuleHom.id, LinearMap.id_apply,
        universalElement_coeff]
      rfl

/-- Input-slot naturality of the representing equivalence. -/
theorem equivalence_input_natural
    {X' : Type uX'} {Y' : Type uY'}
    [AddCommGroup X'] [Module ℂ X'] [AddCommGroup Y'] [Module ℂ Y']
    (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (A' : FullJacobiLatticeModule D X') (B' : FullJacobiLatticeModule D Y')
    (J : FullJacobiLatticeModule D Z)
    (f : ModuleHom A' A) (g : ModuleHom B' B)
    (F : homSpace (ActualWeakModuleUniversalField.targetModule A B) J) :
    backward positiveG A' B' J
        (ActualWeakModuleFullIntertwiner.map (H positiveG) f g
          (ModuleHom.id J) (forward positiveG A B J F)) =
      recordEquiv (ActualWeakModuleUniversalField.targetModule A' B') J
        (((recordEquiv (ActualWeakModuleUniversalField.targetModule A B) J).symm F).comp
          ((recordEquiv (ActualWeakModuleUniversalField.targetModule A' B')
            (ActualWeakModuleUniversalField.targetModule A B)).symm
            (inputMap positiveG A B A' B' f g))) := by
  apply forward_injective positiveG A' B' J
  rw [forward_backward]
  apply Subtype.ext
  apply ActualWeakModuleFullIntertwiner.fields_ext
  intro x y q
  simp only [ActualWeakModuleFullIntertwiner.map_coeff, forward_coeff,
    ModuleHom.id, LinearMap.id_apply]
  have hfield := congrArg (fun I : FullFields positiveG A' B'
      (ActualWeakModuleUniversalField.targetModule A B) => (I.val x).coeff q y)
    (inputMap_field_preserving positiveG A B A' B' f g)
  simp only [forward_coeff, ActualWeakModuleFullIntertwiner.map_coeff,
    ModuleHom.id, LinearMap.id_apply, universalElement_coeff] at hfield
  change F.val ((ActualWeakModuleUniversalField.U A B positiveG
      (f.linearMap x)).coeff q (g.linearMap y)) =
    F.val ((inputMap positiveG A B A' B' f g).val
      ((ActualWeakModuleUniversalField.U A' B' positiveG x).coeff q y))
  exact congrArg F.val hfield.symm

set_option maxHeartbeats 2000000 in
-- Nested independent-universe product Hom types require additional elaboration steps.
/-- Composition of the actual input maps.  The middle equality is the generic
map_comp law; the final equality is the already proved input-slot naturality
applied with the intermediate target P(A',B'). -/
theorem inputMap_comp
    {X' : Type uX'} {Y' : Type uY'}
    [AddCommGroup X'] [Module ℂ X'] [AddCommGroup Y'] [Module ℂ Y']
    {X'' : Type uX''} {Y'' : Type uY''}
    [AddCommGroup X''] [Module ℂ X''] [AddCommGroup Y''] [Module ℂ Y'']
    (positiveG : (gramReal D).PosDef)
    (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (A' : FullJacobiLatticeModule D X') (B' : FullJacobiLatticeModule D Y')
    (A'' : FullJacobiLatticeModule D X'') (B'' : FullJacobiLatticeModule D Y'')
    (f : ModuleHom A' A) (g : ModuleHom B' B)
    (f' : ModuleHom A'' A') (g' : ModuleHom B'' B') :
    inputMap positiveG A B A'' B'' (f.comp f') (g.comp g') =
      recordEquiv (ActualWeakModuleUniversalField.targetModule A'' B'')
        (ActualWeakModuleUniversalField.targetModule A B)
        (((recordEquiv (ActualWeakModuleUniversalField.targetModule A' B')
            (ActualWeakModuleUniversalField.targetModule A B)).symm
            (inputMap positiveG A B A' B' f g)).comp
          ((recordEquiv (ActualWeakModuleUniversalField.targetModule A'' B'')
            (ActualWeakModuleUniversalField.targetModule A' B')).symm
            (inputMap positiveG A' B' A'' B'' f' g'))) := by
  apply forward_injective positiveG A'' B''
    (ActualWeakModuleUniversalField.targetModule A B)
  calc
    forward positiveG A'' B'' (ActualWeakModuleUniversalField.targetModule A B)
        (inputMap positiveG A B A'' B'' (f.comp f') (g.comp g')) =
      ActualWeakModuleFullIntertwiner.map (H positiveG) (f.comp f') (g.comp g')
        (ModuleHom.id (ActualWeakModuleUniversalField.targetModule A B))
        (universalElement positiveG A B) :=
      inputMap_field_preserving positiveG A B A'' B'' (f.comp f') (g.comp g')
    _ = ActualWeakModuleFullIntertwiner.map (H positiveG) f' g'
        (ModuleHom.id (ActualWeakModuleUniversalField.targetModule A B))
        (ActualWeakModuleFullIntertwiner.map (H positiveG) f g
          (ModuleHom.id (ActualWeakModuleUniversalField.targetModule A B))
          (universalElement positiveG A B)) := by
      simpa only [LinearMap.comp_apply, ModuleHom.comp, ModuleHom.id,
        LinearMap.id_comp, LinearMap.comp_id] using
        congrArg (fun T => T (universalElement positiveG A B))
          (ActualWeakModuleFullIntertwiner.map_comp (H positiveG) f g
            (ModuleHom.id (ActualWeakModuleUniversalField.targetModule A B)) f' g'
            (ModuleHom.id (ActualWeakModuleUniversalField.targetModule A B)))
    _ = ActualWeakModuleFullIntertwiner.map (H positiveG) f' g'
        (ModuleHom.id (ActualWeakModuleUniversalField.targetModule A B))
        (forward positiveG A' B' (ActualWeakModuleUniversalField.targetModule A B)
          (inputMap positiveG A B A' B' f g)) := by
      rw [inputMap_field_preserving]
    _ = forward positiveG A'' B'' (ActualWeakModuleUniversalField.targetModule A B)
        (recordEquiv (ActualWeakModuleUniversalField.targetModule A'' B'')
          (ActualWeakModuleUniversalField.targetModule A B)
          (((recordEquiv (ActualWeakModuleUniversalField.targetModule A' B')
              (ActualWeakModuleUniversalField.targetModule A B)).symm
              (inputMap positiveG A B A' B' f g)).comp
            ((recordEquiv (ActualWeakModuleUniversalField.targetModule A'' B'')
              (ActualWeakModuleUniversalField.targetModule A' B')).symm
              (inputMap positiveG A' B' A'' B'' f' g')))) := by
      have hn := equivalence_input_natural positiveG A' B' A'' B''
        (ActualWeakModuleUniversalField.targetModule A B) f' g'
        (inputMap positiveG A B A' B' f g)
      exact (forward_backward positiveG A'' B''
        (ActualWeakModuleUniversalField.targetModule A B) _).symm.trans
        (congrArg (forward positiveG A'' B''
          (ActualWeakModuleUniversalField.targetModule A B)) hn)

end D5.S3.VertexAlgebra.Modules.ActualWeakModuleIntertwinerRepresentability
