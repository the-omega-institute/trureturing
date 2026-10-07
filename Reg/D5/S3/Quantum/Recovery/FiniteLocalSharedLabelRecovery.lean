import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery
open _root_.D5.S3.Quantum.Recovery
open _root_.D5.S3.Quantum.Recovery.FiniteLocalProtocol
open _root_.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery
open _root_.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry
open _root_.D5.S3.Quantum.Recovery.ProductPrefixRigidity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped BigOperators MatrixOrder ComplexOrder
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev signature : Signature where
  Params := (Y : Type) × (P : ActualProtocol Y) × (Y → Prop)
  State p := Accepted p.2.1 p.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def sourceStatement : Prop :=
  ∀ {Y : Type} (P : ActualProtocol Y) (r : ℝ)
      (hr : 0 < r)
      (accept : Y → Prop) (U : Y → Matrix.unitaryGroup (Fin 5) ℂ)
      (p : ℝ) (hp : 0 ≤ p)
      (recovery : ∀ X : Matrix (Fin 5) (Fin 5) ℂ,
        acceptedMap P r accept U X = (p : ℂ) • X),
      p ≤ 1 ∧ InputEffectTreeLaws P ∧ NormalizedInputTreeLaws P ∧ PhysicalReferenceLaws P r U ∧
      (∀ q : ℝ,
        (∀ X : Matrix (Fin 5) (Fin 5) ℂ, acceptedMap P r accept U X = (q : ℂ) • X) ↔
        (∀ (F : Type) [Fintype F] [DecidableEq F]
          (X : Matrix (F × Fin 5) (F × Fin 5) ℂ),
          referenceAcceptedMap P r accept U F X = (q : ℂ) • X)) ∧
      (∀ w : P.tree.Leaves, leafEffect P w = 0 →
        ∀ (F : Type) [Fintype F] [DecidableEq F]
          (X : Matrix (F × Fin 5) (F × Fin 5) ℂ),
          referenceCorrectedHistory P r U F w X = 0) ∧
      (1/2 < r^2 → r^2 < 2 →
        p = h r * ∑ w : Accepted P accept, effectWeight (leafFactors P w.val)) ∧
      ∀ w : Accepted P accept,
        (∃ c : ℝ, 0 ≤ c ∧ (∀ X : Matrix (Fin 5) (Fin 5) ℂ,
          correctedHistory P r U w.val X = (c : ℂ) • X) ∧
        (∀ (F : Type) [Fintype F] [DecidableEq F]
          (X : Matrix (F × Fin 5) (F × Fin 5) ℂ),
          referenceCorrectedHistory P r U F w.val X = (c : ℂ) • X)) ∧
        (p = 0 → leafEffect P w.val = 0) ∧
        (leafEffect P w.val ≠ 0 →
          (ProductPrefixRigidity.gram ((leafFactors P w.val).matrix 0)).rank = 1 ∧
          (ProductPrefixRigidity.gram ((leafFactors P w.val).matrix 1)).rank = 1 ∧
          (1/2 < r^2 → r^2 < 2 →
            0 < effectWeight (leafFactors P w.val) ∧
            (localBloch (leafFactors P w.val) 0,localBloch (leafFactors P w.val) 1) ∈ K_s r ∧
            ∀ (F : Type) [Fintype F] [DecidableEq F]
              (X : Matrix (F × Fin 5) (F × Fin 5) ℂ),
              referenceCorrectedHistory P r U F w.val X =
                ((effectWeight (leafFactors P w.val) * h r : ℝ) : ℂ) • X))

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {Y : Type} (P : ActualProtocol Y) (r : ℝ)
        (hr : 0 < r)
        (accept : Y → Prop) (U : Y → Matrix.unitaryGroup (Fin 5) ℂ)
        (p : ℝ) (hp : 0 ≤ p)
        (recovery : ∀ X : Matrix (Fin 5) (Fin 5) ℂ,
          acceptedMap P r accept U X = (p : ℂ) • X),
        p ≤ 1 ∧ InputEffectTreeLaws P ∧ NormalizedInputTreeLaws P ∧ PhysicalReferenceLaws P r U ∧
        (∀ q : ℝ,
          (∀ X : Matrix (Fin 5) (Fin 5) ℂ, acceptedMap P r accept U X = (q : ℂ) • X) ↔
          (∀ (F : Type) [Fintype F] [DecidableEq F]
            (X : Matrix (F × Fin 5) (F × Fin 5) ℂ),
            referenceAcceptedMap P r accept U F X = (q : ℂ) • X)) ∧
        (∀ w : P.tree.Leaves, leafEffect P w = 0 →
          ∀ (F : Type) [Fintype F] [DecidableEq F]
            (X : Matrix (F × Fin 5) (F × Fin 5) ℂ),
            referenceCorrectedHistory P r U F w X = 0) ∧
        (1/2 < r^2 → r^2 < 2 →
          p = h r * ∑ w : Accepted P accept, effectWeight (leafFactors P w.val)) ∧
        ∀ w : Accepted P accept,
          (∃ c : ℝ, 0 ≤ c ∧ (∀ X : Matrix (Fin 5) (Fin 5) ℂ,
            correctedHistory P r U w.val X = (c : ℂ) • X) ∧
          (∀ (F : Type) [Fintype F] [DecidableEq F]
            (X : Matrix (F × Fin 5) (F × Fin 5) ℂ),
            referenceCorrectedHistory P r U F w.val X = (c : ℂ) • X)) ∧
          (p = 0 → R.readout () ⟨Y,P,accept⟩ w = 0) ∧
          (leafEffect P w.val ≠ 0 →
            (ProductPrefixRigidity.gram ((leafFactors P w.val).matrix 0)).rank = 1 ∧
            (ProductPrefixRigidity.gram ((leafFactors P w.val).matrix 1)).rank = 1 ∧
            (1/2 < r^2 → r^2 < 2 →
              0 < effectWeight (leafFactors P w.val) ∧
              (localBloch (leafFactors P w.val) 0,localBloch (leafFactors P w.val) 1) ∈ K_s r ∧
              ∀ (F : Type) [Fintype F] [DecidableEq F]
                (X : Matrix (F × Fin 5) (F × Fin 5) ℂ),
                referenceCorrectedHistory P r U F w.val X =
                  ((effectWeight (leafFactors P w.val) * h r : ℝ) : ℂ) • X))

def actual : Realization signature :=
  realize signature (fun _ p w => leafEffect p.2.1 w.val) (fun e => nomatch e)

theorem actual_law : arena.Law actual := by
  intro Y P r hr accept U p hp recovery
  exact actual_shared_label_support_rigidity P r hr accept U p hp recovery

theorem source_bridge : sourceStatement ↔ arena.Law actual := Iff.rfl

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

namespace AuditModel
set_option backward.isDefEq.respectTransparency false

def cpZero (n : ℕ) : CompletelyPositiveMap (CStarMatrix (Fin n) (Fin n) ℂ)
    (CStarMatrix (Fin n) (Fin n) ℂ) where
  toLinearMap := 0
  map_cstarMatrix_nonneg' k M hM := by
    change 0 ≤ (0 : CStarMatrix (Fin k) (Fin k) (CStarMatrix (Fin n) (Fin n) ℂ))
    exact le_rfl

def cpId (n : ℕ) : CompletelyPositiveMap (CStarMatrix (Fin n) (Fin n) ℂ)
    (CStarMatrix (Fin n) (Fin n) ℂ) where
  toLinearMap := LinearMap.id
  map_cstarMatrix_nonneg' k M hM := by
    change 0 ≤ M
    exact hM

abbrev ancillas : ProductAncillas (Fin 2) where
  dimension := fun _ => 1
  density := fun _ => ⟨1,by exact ⟨zero_le_one,by norm_num [Matrix.trace]⟩⟩

abbrev instrument : Instrument (fun a => InputDimensions a * ancillas.dimension a) where
  actor := 0
  outcomes := 2
  output := fun _ a => InputDimensions a * ancillas.dimension a
  unchanged := fun _ _ _ => rfl
  operation := fun y => if y=0 then cpZero 2 else cpId 2
  trace_preserving X := by
    simp only [Fin.sum_univ_two, if_pos rfl, if_neg (by decide : (1 : Fin 2) ≠ 0)]
    change trace (action (cpZero 2) X) + trace (action (cpId 2) X) = trace X
    have hz : action (cpZero 2) X = 0 := rfl
    have hi : action (cpId 2) X = X := rfl
    rw [hz,hi]
    simp

abbrev protocol : ActualProtocol (Fin 2) where
  ancillas := ancillas
  tree := .node instrument (fun y => .leaf y)

def zeroLeaf : protocol.tree.Leaves := ⟨0,()⟩
def idLeaf : protocol.tree.Leaves := ⟨1,()⟩
def zeroAccept : Fin 2 → Prop := fun y => y=0
def corrections : Fin 2 → Matrix.unitaryGroup (Fin 5) ℂ := fun _ => 1

def zeroState : Accepted protocol zeroAccept := ⟨zeroLeaf,rfl⟩

theorem recovery_zero (X : Matrix (Fin 5) (Fin 5) ℂ) : acceptedMap protocol 1 zeroAccept corrections X = 0 := by
  classical
  unfold acceptedMap
  apply Finset.sum_eq_zero
  intro w _
  rcases w with ⟨⟨y,⟨⟩⟩,hy⟩
  change y=0 at hy
  subst y
  have hz (M : State (Fin 5) (fun a => InputDimensions a * ancillas.dimension a)) :
      step instrument 0 M = 0 := by
    ext i j
    rfl
  simp only [correctedHistory,historyMap,corrections,protocol,Tree.branch]
  rw [hz]
  simp only [OneMemClass.coe_one, one_mul, conjTranspose_one, mul_one]
  change recordTrace (0 : State (Fin 5) (fun a => InputDimensions a * ancillas.dimension a)) = 0
  ext i j
  simp [recordTrace]

theorem zero_effect : leafEffect protocol zeroLeaf = 0 := by
  have result := actual_shared_label_support_rigidity protocol 1 (by norm_num)
    zeroAccept corrections 0 (by norm_num) (by intro X; simpa using recovery_zero X)
  exact (result.2.2.2.2.2.2.2 zeroState).2.1 rfl

theorem id_effect : leafEffect protocol idLeaf = 1 := by
  classical
  have result := actual_shared_label_support_rigidity protocol 1 (by norm_num)
    zeroAccept corrections 0 (by norm_num) (by intro X; simpa using recovery_zero X)
  have complete := result.2.1.2.2.2.2.1 protocol.tree (protocol.ancillas.rootFactors InputDimensions)
  rw [result.2.1.2.1] at complete
  ext i j
  have hc := congrArg (fun M => M (pairCoordinates i) (pairCoordinates j)) complete
  simp only [Tree.descendantEffect, protocol, Tree.Leaves, Fintype.sum_sigma,
    Fintype.sum_unique, Fin.sum_univ_two, Matrix.add_apply] at hc
  change leafEffect protocol zeroLeaf i j + leafEffect protocol idLeaf i j = _ at hc
  rw [zero_effect] at hc
  simpa only [Matrix.zero_apply, zero_add, Matrix.one_apply, Equiv.apply_eq_iff_eq] using hc
end AuditModel

theorem rejected_law : ¬ arena.Law rejected := by
  intro bad
  have result := bad AuditModel.protocol 1 (by norm_num) AuditModel.zeroAccept
    AuditModel.corrections 0 (by norm_num) (by intro X; simpa using AuditModel.recovery_zero X)
  have falseReadout := (result.2.2.2.2.2.2.2 AuditModel.zeroState).2.1 rfl
  change (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) = 0 at falseReadout
  have hf := congrArg (fun M => M (0,0) (0,0)) falseReadout
  norm_num at hf

set_option maxHeartbeats 1000000 in
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    let accept : Fin 2 → Prop := fun _ => True
    let x : Accepted AuditModel.protocol accept := ⟨AuditModel.zeroLeaf,True.intro⟩
    let y : Accepted AuditModel.protocol accept := ⟨AuditModel.idLeaf,True.intro⟩
    refine ⟨⟨Fin 2,AuditModel.protocol,accept⟩,x,y,?_⟩
    change leafEffect AuditModel.protocol AuditModel.zeroLeaf ≠
      leafEffect AuditModel.protocol AuditModel.idLeaf
    rw [AuditModel.zero_effect,AuditModel.id_effect]
    exact zero_ne_one

set_option maxHeartbeats 1000000 in
noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.actual_shared_label_support_rigidity) (type_of% (realize.{1, 0, 0, 0, 0} signature (fun _ p w => leafEffect p.2.1 w.val) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Recovery") "FiniteLocalSharedLabelRecovery") "actual_shared_label_support_rigidity") "Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery/Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{1, 0, 0, 0, 0} signature (fun _ p w => leafEffect p.2.1 w.val) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery, definition := none, coordinates := #[0, 1, 4], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "body", "arg", "fn", "arg", "body", "fn", "arg"], stateBinder := 9, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `backward.isDefEq.respectTransparency, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxHeartbeats, value := .nat 1000000 }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery, declaration := `D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.actual_shared_label_support_rigidity, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.observationFact0, `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.anchorEnumeration }


#print axioms actual_law
#print axioms source_bridge
#print axioms registration

end
end Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery


noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{1, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.arena
noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalSharedLabelRecovery\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalSharedLabelRecovery\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{1, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.arena
noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalSharedLabelRecovery\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalSharedLabelRecovery\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{1, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{1, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.arena
    Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.sourceStatement
    Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration)

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalSharedLabelRecovery\",\"actual_shared_label_support_rigidity\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalSharedLabelRecovery\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery, declaration := `D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.actual_shared_label_support_rigidity, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{1, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.arena
  Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.sourceStatement
  Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration)

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.observation0 : {Y : Type} →
  (P : D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.ActualProtocol Y) →
    (r : Real) →
      (hr : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r) →
        (accept : Y → Prop) →
          (U :
              Y →
                @Subtype.{1}
                  (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
                  fun
                    (x :
                      Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex) =>
                  @Membership.mem.{0, 0}
                    (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
                    (@Submonoid.{0}
                      (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
                      (@MulZeroOneClass.toMulOneClass.{0}
                        (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
                        (@instMulZeroOneClassOfSemiring.{0}
                          (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
                          (@Matrix.semiring.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                            Complex
                            (@CommSemiring.toSemiring.{0} Complex
                              (@CommRing.toCommSemiring.{0} Complex Complex.commRing))
                            (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                            (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))))
                    (@SetLike.instMembership.{0, 0}
                      (@Submonoid.{0}
                        (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
                        (@MulZeroOneClass.toMulOneClass.{0}
                          (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
                          (@instMulZeroOneClassOfSemiring.{0}
                            (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
                            (@Matrix.semiring.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                              Complex
                              (@CommSemiring.toSemiring.{0} Complex
                                (@CommRing.toCommSemiring.{0} Complex Complex.commRing))
                              (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                              (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))))
                      (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
                      (@Submonoid.instSetLike.{0}
                        (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
                        (@MulZeroOneClass.toMulOneClass.{0}
                          (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
                          (@instMulZeroOneClassOfSemiring.{0}
                            (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
                            (@Matrix.semiring.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                              Complex
                              (@CommSemiring.toSemiring.{0} Complex
                                (@CommRing.toCommSemiring.{0} Complex Complex.commRing))
                              (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                              (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))))
                    (@Matrix.unitaryGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                      (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex
                      Complex.commRing Complex.instStarRing)
                    x) →
            (p : Real) →
              (hp :
                  @LE.le.{0} Real Real.instLE
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) p) →
                (recovery :
                    ∀
                      (X :
                        Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex),
                      @Eq.{1}
                        (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
                        (@D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.acceptedMap Y P r accept U X)
                        (@HSMul.hSMul.{0, 0, 0} Complex
                          (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
                          (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
                          (@instHSMul.{0, 0} Complex
                            (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
                            (@Matrix.smul.{0, 0, 0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex Complex
                              (@instSMulOfMul.{0} Complex Complex.instMul)))
                          (Complex.ofReal p) X)) →
                  (w : @D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.Accepted Y P accept) →
                    @Eq.{1} Real p (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{1, 0, 0, 0, 0}
                        Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.signature PUnit.unit.{1}
                        (@Sigma.mk.{1, 0} Type
                          (fun (Y : Type) =>
                            @Sigma.{0, 0} (D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.ActualProtocol Y)
                              fun (P : D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.ActualProtocol Y) =>
                              Y → Prop)
                          Y
                          (@Sigma.mk.{0, 0} (D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.ActualProtocol Y)
                            (fun (P : D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.ActualProtocol Y) =>
                              Y → Prop)
                            P accept)) :=
  fun {Y : Type} (P : D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.ActualProtocol Y) (r : Real)
    (hr : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r)
    (accept : Y → Prop)
    (U :
      Y →
        @Subtype.{1}
          (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
          fun
            (x :
              Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex) =>
          @Membership.mem.{0, 0}
            (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
            (@Submonoid.{0}
              (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
              (@MulZeroOneClass.toMulOneClass.{0}
                (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
                (@instMulZeroOneClassOfSemiring.{0}
                  (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
                  (@Matrix.semiring.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex
                    (@CommSemiring.toSemiring.{0} Complex (@CommRing.toCommSemiring.{0} Complex Complex.commRing))
                    (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                    (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))))
            (@SetLike.instMembership.{0, 0}
              (@Submonoid.{0}
                (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
                (@MulZeroOneClass.toMulOneClass.{0}
                  (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
                  (@instMulZeroOneClassOfSemiring.{0}
                    (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
                    (@Matrix.semiring.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex
                      (@CommSemiring.toSemiring.{0} Complex (@CommRing.toCommSemiring.{0} Complex Complex.commRing))
                      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                      (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))))
              (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
              (@Submonoid.instSetLike.{0}
                (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
                (@MulZeroOneClass.toMulOneClass.{0}
                  (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
                  (@instMulZeroOneClassOfSemiring.{0}
                    (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
                    (@Matrix.semiring.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex
                      (@CommSemiring.toSemiring.{0} Complex (@CommRing.toCommSemiring.{0} Complex Complex.commRing))
                      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                      (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))))
            (@Matrix.unitaryGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex Complex.commRing
              Complex.instStarRing)
            x)
    (p : Real)
    (hp : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) p)
    (recovery :
      ∀
        (X :
          Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex),
        @Eq.{1}
          (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
          (@D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.acceptedMap Y P r accept U X)
          (@HSMul.hSMul.{0, 0, 0} Complex
            (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
            (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
            (@instHSMul.{0, 0} Complex
              (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex)
              (@Matrix.smul.{0, 0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Complex Complex
                (@instSMulOfMul.{0} Complex Complex.instMul)))
            (Complex.ofReal p) X))
    (w : @D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.Accepted Y P accept)
    (a : @Eq.{1} Real p (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{1, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.signature
    Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.actual PUnit.unit.{1}
    (@Sigma.mk.{1, 0} Type
      (fun (Y : Type) =>
        @Sigma.{0, 0} (D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.ActualProtocol Y)
          fun (P : D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.ActualProtocol Y) => Y → Prop)
      Y
      (@Sigma.mk.{0, 0} (D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.ActualProtocol Y)
        (fun (P : D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.ActualProtocol Y) => Y → Prop) P accept))
    w

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalSharedLabelRecovery\",\"actual_shared_label_support_rigidity\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"body\",\"argument\",\"function\",\"argument\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalSharedLabelRecovery\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery, declaration := `D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.actual_shared_label_support_rigidity, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .argument, .argument, .argument, .argument, .argument, .argument, .body, .argument, .function, .argument, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalSharedLabelRecovery\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalSharedLabelRecovery\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalSharedLabelRecovery\",\"actual_shared_label_support_rigidity\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery, declaration := `D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.actual_shared_label_support_rigidity, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration).actual (Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration).variation.2.choose (Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration).variation.1 (Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalSharedLabelRecovery\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalSharedLabelRecovery\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
