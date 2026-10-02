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
register_information_theorem actual_shared_label_support_rigidity in arena
  readout via (realize signature (fun _ p w => leafEffect p.2.1 w.val) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery
    coordinates := #[0,1,4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "body", "arg", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 9 }] })
  escape continues (open)

#print axioms actual_law
#print axioms source_bridge
#print axioms registration

end
end Reg.D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery
