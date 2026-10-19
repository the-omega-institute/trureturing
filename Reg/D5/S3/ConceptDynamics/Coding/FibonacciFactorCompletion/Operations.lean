import Reg.Support.FibonacciOperations.OriginalOperationCommonStem
import Reg.Support.FibonacciOperations.OriginalEqualWeightCodebook
import Reg.Support.FibonacciOperations.SuppliedCodebookStorageLiminf
import Reg.Support.FibonacciOperations.OriginalCodebookStorageLiminf
import Reg.Support.FibonacciConsensusUniverse
import Reg.Support.FibonacciQuadratic
import Mathlib.Logic.Encodable.Basic
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.ExactOriginal123
noncomputable section


abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => Finset (List Return)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ family => family.card) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (model : Model) (o : Ownership) (b : ℝ) (contract : Contract) (N : ℕ),
    ∃ family : Finset (List Return),
      (∀ xs, xs ∈ family ↔ ActualPairSupply model o b contract xs ∧ listWeight xs = N) ∧
      r.readout () () family = Nat.card {xs : List Return // ActualPairSupply model o b contract xs ∧ listWeight xs = N} ∧
      Finite {xs : List Return // ActualPairSupply model o b contract xs ∧ listWeight xs = N}

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  letI : IsEmpty {xs : List Return // ActualPairSupply .original (fun _ => false) (-1) .closed xs ∧ listWeight xs = 0} := ⟨by
    intro xs
    obtain ⟨err, bound, _⟩ := xs.property.1 .high
    have hb := bound 0
    have hn := abs_nonneg (err 0)
    change |err 0| ≤ -1 at hb
    linarith⟩
  obtain ⟨family, _, eq, _⟩ := h .original (fun _ => false) (-1) .closed 0
  change 1 = Nat.card _ at eq
  simpa using eq

def evidence : Registration sourceArena (type_of% @operation_exact_family) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@operation_exact_family, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), ∅, {[]}, ?_⟩
    simp [actual, realize]

def operation_exact_family_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.operation_exact_family)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ family => family.card) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.ExactOriginal123.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.ExactOriginal123.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ family => family.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms operation_exact_family_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.ExactOriginal123

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.ExactOriginal122
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ state => state) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (model : Model) (o : Ownership) (b : ℝ)
    (contract : Contract) (xs : List Return) (supply : ActualPairSupply model o b contract xs)
    (j : Side),
OperationRecord o (r.readout () () b) contract (source j model xs)
      (OperationPairedRecord model o xs j) ∧ OperationFiniteSource (source j model xs)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨b, _, _, supply⟩ :=
    Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.SupplyWitnesses.empty_strict_supply
      (fun _ => false)
  have bad := (h .original (fun _ => false) b .strict [] supply .high).1
  obtain ⟨x, _, err, herr, _⟩ := bad
  have hb := herr 0
  change |err 0| < (-1 : ℝ) at hb
  linarith [abs_nonneg (err 0)]

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.operation_pair_membership) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.operation_pair_membership, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def operation_pair_membership_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.operation_pair_membership)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ state => state) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.ExactOriginal122.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.ExactOriginal122.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ state => state) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms operation_pair_membership_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.ExactOriginal122

open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.OriginalOperationDecoderStorage
noncomputable section
universe u

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => Finset (List Return)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ family => family.card) (fun e => nomatch e)

def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ {Configuration : Type*}
    (action : Configuration → Op Configuration Color Label) (initialConfiguration : Configuration)
    (model : Model) (o : Ownership) (b : ℝ) (contract : Contract) (N : ℕ)
    (processing : Processing action initialConfiguration (OperationRecord o b contract))
    (safety : ∀ a r, OperationRecord o b contract a r → ∀ t,
      Run action (full r) ⟨initialConfiguration,0,[]⟩ t →
      ∀ p (hp : p < t.output.length), t.output[p] = a p)
    (liveness : ∀ a r, OperationRecord o b contract a r → OperationFiniteSource a → ∀ p,
      ∃ t, Run action (full r) ⟨initialConfiguration,0,[]⟩ t ∧ p < t.output.length)
    (encoding : Configuration → List Bool)
    (faithful : Set.InjOn encoding {c | ∃ H,
      ReachThrough action initialConfiguration (OperationRecord o b contract) H c}),
    let X := {xs : List Return // ActualPairSupply model o b contract xs ∧ listWeight xs = N}
    letI := Classical.decEq Configuration
    ∃ (family : Finset (List Return)) (cuts : X → Frame Configuration Label),
      (∀ xs, xs ∈ family ↔ ActualPairSupply model o b contract xs ∧ listWeight xs = N) ∧
      r.readout () () family = Nat.card X ∧
      (∀ x, Cut action initialConfiguration (history model x.val) (cuts x) ∧
        (∀ t, Cut action initialConfiguration (history model x.val) t → t = cuts x) ∧
        (cuts x).acquired = observationOffset model + N ∧ (cuts x).output = [] ∧
        ReachThrough action initialConfiguration (OperationRecord o b contract)
          (observationOffset model + N) (cuts x).state) ∧
      Function.Injective (fun x => (cuts x).state) ∧
      (∃ states : Finset Configuration, states.card = Nat.card X ∧
        ∀ c, c ∈ states ↔ ∃ x, (cuts x).state = c) ∧
      (∀ B : ℕ, Peak action initialConfiguration (OperationRecord o b contract) encoding
        (observationOffset model + N) ≤ (B : WithTop ℕ) → Nat.card X ≤ 2^(B+1)-1) ∧
      (∀ B : ℕ, (∀ x, (encoding (cuts x).state).length = B) → Nat.card X ≤ 2^B) ∧
      Monotone (Peak action initialConfiguration (OperationRecord o b contract) encoding) ∧
      (∀ a r t vertices, OperationRecord o b contract a r →
        Trace action (full r) ⟨initialConfiguration,0,[]⟩ t vertices →
        t.acquired ≤ observationOffset model+N → ∀ c ∈ vertices,
          ((encoding c).length : WithTop ℕ) ≤
            Peak action initialConfiguration (OperationRecord o b contract) encoding
              (observationOffset model+N))

/-- One legal common budget supplies both original sides and the decoder hypotheses. -/
theorem joint_supply_witness (o : Ownership) :
    ∃ b : ℝ, 0 ≤ b ∧ b < lam ∧ ActualPairSupply .original o b .closed [] := by
  have bounds := Reg.Support.FibonacciQuadratic.t_bounds
  have gp : 0 < g := by dsimp [g]; linarith [bounds.1]
  have gq : g < 1 / 4 := by dsimp [g]; linarith [bounds.2]
  have g1 : g < 1 := by linarith
  have rp : 0 < rho := pow_pos gp 6
  have r1 : rho < 1 := pow_lt_one₀ gp.le g1 (by decide)
  have cp : 0 < chi := pow_pos gp 20
  have scale : 0 < g^2 * chi := mul_pos (sq_pos_of_pos gp) cp
  have hp : 0 < hSide .high := by dsimp [hSide]; linarith
  have ap : 0 < aSide .high := mul_pos (sub_pos.mpr r1) hp
  have geometry := (actual_complete_boundary_geometry .original []).1 .high 0
  have xp : 0 < xSide .high := ap.trans (by simpa [execute, initial] using geometry.1)
  have x1 : xSide .high < 1 := by
    have xh : xSide .high < hSide .high := by simpa [execute, initial] using geometry.2
    have h1 : hSide .high < 1 := by dsimp [hSide]; linarith
    exact xh.trans h1
  have scaleSmall : g^2 * chi < rho := by
    have p16 : g^16 < 1 := pow_lt_one₀ gp.le g1 (by decide)
    calc
      g^2 * chi = g^6 * g^16 := by dsimp [chi]; rw [← pow_add, ← pow_add]
      _ < g^6 * 1 := mul_lt_mul_of_pos_left p16 (pow_pos gp 6)
      _ = rho := by simp [rho]
  let loss := g^2 * chi * xSide .high
  have lp : 0 < loss := mul_pos scale xp
  have lossScale : loss < g^2 * chi := by
    simpa [loss] using mul_lt_mul_of_pos_left x1 scale
  have lr : loss < rho := lossScale.trans scaleSmall
  have rhoSmall : rho < 1 / 4096 := by
    have hh := pow_lt_pow_left₀ gq gp.le (by decide : (6 : ℕ) ≠ 0)
    norm_num [rho] at hh ⊢
    exact hh
  have lamLower : 3 / 80 < lam := by dsimp [lam, T2]; linarith [bounds.2]
  let b := lam - loss / 2
  have hb : lam - rho < b := by dsimp [b]; linarith
  have bp : 0 ≤ b := by linarith
  have bl : b < lam := by dsimp [b]; linarith
  have cost : lam - g^2 * chi * xSide .high < b := by change lam - loss < b; dsimp [b]; linarith
  have strict : ActualPairSupply .original o b .strict [] :=
    (actual_strict_cost_supply .original o b [] hb).mpr
      ⟨by simpa [execute, initial] using cost, (by intro impossible; cases impossible), trivial⟩
  refine ⟨b, bp, bl, ?_⟩
  intro j
  obtain ⟨err, bound, observed, zero, future⟩ := strict j
  exact ⟨err, (fun p => (bound p).le), observed, zero, future⟩

/-- The changed complete Law fails at an inhabited original operational tuple. -/
theorem rejected_law : ¬ sourceArena.{u}.Law rejected := by
  classical
  intro h
  let o : Ownership := fun _ => false
  obtain ⟨b, bp, bl, supply⟩ := joint_supply_witness o
  let action := Reg.Support.FibonacciConsensusUniverse.action.{u} b
  let initialConfiguration := Reg.Support.FibonacciConsensusUniverse.initial.{u}
  letI : Encodable Reg.Support.FibonacciConsensusUniverse.Configuration.{u} :=
    Encodable.ofCountable _
  let encoding : Reg.Support.FibonacciConsensusUniverse.Configuration.{u} → List Bool :=
    fun c => List.replicate (Encodable.encode c) true
  have injection : Function.Injective encoding := by
    intro c d eq
    apply Encodable.encode_injective
    simpa [encoding] using congrArg List.length eq
  have processing : Processing action initialConfiguration (OperationRecord o b .closed) :=
    ⟨⟨_, ⟨[initialConfiguration], .refl⟩, Or.inr ⟨_, rfl⟩⟩,
      Reg.Support.FibonacciConsensusUniverse.postprocessing o b⟩
  have safety := Reg.Support.FibonacciConsensusUniverse.safety.{u} o b bp
  have liveness := Reg.Support.FibonacciConsensusUniverse.liveness.{u} o b bp bl
  have faithful : Set.InjOn encoding {c | ∃ H,
      ReachThrough action initialConfiguration (OperationRecord o b .closed) H c} :=
    injection.injOn
  let X := {xs : List Return // ActualPairSupply .original o b .closed xs ∧ listWeight xs = 0}
  obtain ⟨_, _, _, finite⟩ := operation_exact_family .original o b .closed 0
  letI : Finite X := finite
  letI : Nonempty X := ⟨⟨[], supply, rfl⟩⟩
  have positive : 0 < Nat.card X := Nat.card_pos
  obtain ⟨family, cuts, membership, card, rest⟩ := h action initialConfiguration
    .original o b .closed 0 processing safety liveness encoding faithful
  change 0 = Nat.card X at card
  exact (Nat.ne_of_gt positive) card.symm

def evidence : Registration sourceArena.{u} (type_of% @original_operation_decoder_storage) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@original_operation_decoder_storage, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), ∅, {[]}, ?_⟩
    simp [actual, realize]

def original_operation_decoder_storage_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.original_operation_decoder_storage.{u})
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ family => family.card) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.OriginalOperationDecoderStorage.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.OriginalOperationDecoderStorage.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ family => family.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 14
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms joint_supply_witness
#print axioms rejected_law
#print axioms evidence
#print axioms original_operation_decoder_storage_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.OriginalOperationDecoderStorage

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.OriginalOperationCommonStem
noncomputable section
universe u v

theorem rejected_complete_law : ¬ sourceArena.{u,v}.Law rejected := by
  obtain ⟨b, bp, bl, supply⟩ := OriginalOperationDecoderStorage.joint_supply_witness (fun _ => false)
  exact rejected_law b bp bl supply

def evidence : Registration sourceArena.{u,v} (type_of% @original_operation_common_stem.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@original_operation_common_stem.{u,v}, rejected, rejected_complete_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_complete_law
  dependence := by
    intro i
    exact ⟨(), [], [Label.L0], by simp [actual, realize]⟩

def original_operation_common_stem_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.original_operation_common_stem.{u,v})
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ w => w.length+1) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.OriginalOperationCommonStem.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.OriginalOperationCommonStem.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena.{u,v}⟩
  objectArena := .source ⟨sourceArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena.{u,v} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ w => w.length+1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "body", "arg", "body", "arg", "arg", "arg",
        "arg", "arg"]
      stateBinder := 16
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_operation_common_stem_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.OriginalOperationCommonStem

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.OriginalEqualWeightCodebook
noncomputable section

def original_equal_weight_codebook_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.original_equal_weight_codebook)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ R => R.r) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.OriginalEqualWeightCodebook.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.OriginalEqualWeightCodebook.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ R => R.r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "arg", "body",
        "fn", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_equal_weight_codebook_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.OriginalEqualWeightCodebook

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.SuppliedCodebookStorageLiminf
noncomputable section
universe u

def supplied_codebook_storage_liminf_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.supplied_codebook_storage_liminf.{u})
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ B => (B : ℝ)) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.SuppliedCodebookStorageLiminf.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.SuppliedCodebookStorageLiminf.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena.{u}⟩
  objectArena := .source ⟨sourceArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ B => (B : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn",
        "arg", "body", "body", "body", "body", "arg"]
      stateBinder := 24
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms supplied_codebook_storage_liminf_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.SuppliedCodebookStorageLiminf

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.OriginalCodebookStorageLiminf
noncomputable section
universe u

def original_codebook_storage_liminf_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.original_codebook_storage_liminf.{u})
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ R => R.r) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.OriginalCodebookStorageLiminf.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.OriginalCodebookStorageLiminf.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena.{u}⟩
  objectArena := .source ⟨sourceArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ R => R.r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg",
        "body", "fn", "arg", "fn", "arg"]
      stateBinder := 15
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_codebook_storage_liminf_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.OriginalCodebookStorageLiminf
