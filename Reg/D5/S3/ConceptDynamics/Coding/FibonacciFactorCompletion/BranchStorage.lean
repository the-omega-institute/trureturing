import Reg.Support.FibonacciBranchStorageWitness.Realization
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage.ExactOriginal41
noncomputable section
universe u_1
open BranchStorage Operations
open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ B => 2^(B+1)-1) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ {Configuration : Type u_1} {n k H : ℕ}
    (action : Configuration → Op Configuration Color Label) (initialConfiguration : Configuration)
    (o : Ownership) (b : ℝ) (encoding : Configuration → List Bool)
    (faithful : Set.InjOn encoding {c | ∃ M,
      ReachThrough action initialConfiguration (OperationRecord o b .closed) M c})
    (cuts : (Fin n → Bool) → Frame Configuration Label) (stem : List Label)
    (joint : Function.Injective (fun z => ((cuts z).state,(cuts z).output)))
    (bounded : ∀ z, (cuts z).output.length ≤ k)
    (output : ∀ z, (cuts z).output = stem.take (cuts z).output.length)
    (reached : ∀ z, ReachThrough action initialConfiguration (OperationRecord o b .closed) H (cuts z).state)
    (B : ℕ) (peak : Peak action initialConfiguration (OperationRecord o b .closed) encoding H ≤ (B : WithTop ℕ)) ,
    2^n ≤ r.readout () () B*(k+1)


theorem rejected_law : ¬ sourceArena.{u_1}.Law rejected := by
  intro h
  let C := ULift.{u_1} Unit
  let c : C := ⟨()⟩
  let action : C → Op C Color Label := fun _ => .stopped
  let cuts : (Fin 0 → Bool) → Frame C Label := fun _ => ⟨c, 0, []⟩
  obtain ⟨b, _, _, strict⟩ := Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.SupplyWitnesses.empty_strict_supply (fun _ => false)
  have closed : ActualPairSupply .original (fun _ => false) b .closed [] := by
    intro j
    obtain ⟨err, bound, rest⟩ := strict j
    exact ⟨err, fun p => (bound p).le, rest⟩
  have record := (operation_pair_membership .original (fun _ => false) b .closed [] closed .high).1
  have reached : ∀ z, ReachThrough action c (OperationRecord (fun _ => false) b .closed) 0 (cuts z).state := by
    intro z
    exact ⟨_, _, ⟨c, 0, []⟩, record, ⟨_, .refl⟩, le_rfl, rfl⟩
  have peak : Peak action c (OperationRecord (fun _ => false) b .closed) (fun _ => []) 0 ≤ (0 : WithTop ℕ) := by
    exact iSup_le fun _ => iSup_le fun _ => le_rfl
  have impossible := @h C 0 0 0 action c (fun _ => false) b (fun _ => [])
    (by intro x hx y hy eq; exact Subsingleton.elim x y) cuts []
    (by intro x y eq; exact Subsingleton.elim x y)
    (by intro z; exact le_rfl) (by intro z; rfl) reached 0 peak
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena.{u_1} (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage.common_stem_code_capacity.{u_1}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage.common_stem_code_capacity.{u_1}, rejected, rejected_law⟩
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
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def common_stem_code_capacity_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage.common_stem_code_capacity.{u_1})
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ B => 2^(B+1)-1) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage.ExactOriginal41.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage.ExactOriginal41.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena.{u_1}⟩
  objectArena := .source ⟨sourceArena.{u_1}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena.{u_1} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ B => 2^(B+1)-1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 16
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms common_stem_code_capacity_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage.ExactOriginal41

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage.NondegenerateOriginal
noncomputable section
universe u_1
open BranchStorage Operations
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open Reg.Support.FibonacciBranchStorageWitness
open Filter

def WholeLaw (factor : ℕ → ℕ) : Prop := ∀ {Configuration : Type u_1}
    (action : Configuration → Op Configuration Color Label) (initialConfiguration : Configuration)
    (o : Ownership) (b : ℝ)
    (s1 s2 : Guard) (P Q : List Label) (h : List Color)
    (hP : LegalWord .G0 s1 P) (hQ : LegalWord .G0 s2 Q)
    (hPlen : P.length = h.length) (hQlen : Q.length = h.length)
    (U V : Bool → List Label) (W : Bool → List Color)
    (L : ℕ) (hL : 0 < L)
    (hU : ∀ i, LegalWord s1 s1 (U i)) (hV : ∀ i, LegalWord s2 s2 (V i))
    (hUlen : ∀ i, (U i).length = L) (hVlen : ∀ i, (V i).length = L)
    (hWlen : ∀ i, (W i).length = L)
    (differentU : U false ≠ U true) (differentV : V false ≠ V true)
    (hbudget : familyEndpointBudget P Q h U V W L ≤ b)
    (k : ℕ) (hk : k < P.length)
    (sameStem : ∀ p (hp : p < k), P[p] = Q[p]'(by omega))
    (differentStem : P[k] ≠ Q[k]'(by omega))
    (safety : ∀ a r, OperationRecord o b .closed a r → ∀ t,
      Run action (full r) ⟨initialConfiguration,0,[]⟩ t →
      ∀ p (hp : p < t.output.length), t.output[p] = a p)
    (liveness : ∀ a r, OperationRecord o b .closed a r → OperationFiniteSource a → ∀ p,
      ∃ t, Run action (full r) ⟨initialConfiguration,0,[]⟩ t ∧ p < t.output.length)
    (postprocessing : ∀ a r, OperationRecord o b .closed a r →
      ∀ (c d : Configuration) (q : ℕ) (out batch : List Label)
      (f : Color → Option (Configuration × List Label)),
      Run action (full r) ⟨initialConfiguration,0,[]⟩ ⟨c,q,out⟩ →
      action c = .acquire f → f (r q) = some (d,batch) →
      ∃ t, Drain action ⟨d,q+1,out++batch⟩ t)
    (encoding : Configuration → List Bool)
    (faithful : Set.InjOn encoding {c | ∃ H,
      ReachThrough action initialConfiguration (OperationRecord o b .closed) H c}),
    ∃ (e1 e2 : Guard) (w1 w2 : List Label),
      LegalWord s1 e1 w1 ∧ LegalWord s2 e2 w2 ∧
      canonicalReturnLo U L < coordinate w1 0 ∧ coordinate w1 0 < canonicalReturnHi U L ∧
      canonicalReturnLo V L < coordinate w2 0 ∧ coordinate w2 0 < canonicalReturnHi V L ∧
      (∃ tailPath1 tailPath2 : ℕ → Guard,
        LiteralTailPath s1 w1 tailPath1 ∧ LiteralTailPath s2 w2 tailPath2 ∧
        ∀ (n : ℕ) (z : Fin n → Bool), ∃ path1 path2 : ℕ → Guard,
          LiteralTailSplice (synchronousPrefix P U z) w1 path1 tailPath1 ∧
          LiteralTailSplice (synchronousPrefix Q V z) w2 path2 tailPath2) ∧
      (∀ n : ℕ, ∃ (cuts : (Fin n → Bool) → Frame Configuration Label) (states : Finset Configuration),
        (∀ z : Fin n → Bool,
          OperationRecord o b .closed (address (synchronousPrefix P U z++w1))
            (recordWithTail o (synchronousPrefix h W z) w1) ∧
          OperationFiniteSource (address (synchronousPrefix P U z++w1)) ∧
          OperationRecord o b .closed (address (synchronousPrefix Q V z++w2))
            (recordWithTail o (synchronousPrefix h W z) w2)) ∧
        (∀ z : Fin n → Bool, ∀ p,
          address (synchronousPrefix P U z++w1) (P.length+n*L+p) = address w1 p ∧
          coordinate (synchronousPrefix P U z++w1) (P.length+n*L+p) = coordinate w1 p ∧
          address (synchronousPrefix Q V z++w2) (P.length+n*L+p) = address w2 p ∧
          coordinate (synchronousPrefix Q V z++w2) (P.length+n*L+p) = coordinate w2 p ∧
          recordWithTail o (synchronousPrefix h W z) w1 (P.length+n*L+p) = observe o (coordinate w1 p) 0 ∧
          recordWithTail o (synchronousPrefix h W z) w2 (P.length+n*L+p) = observe o (coordinate w2 p) 0) ∧
        Function.Injective (fun z : Fin n → Bool => address (synchronousPrefix P U z++w1)) ∧
        (∀ z, Cut action initialConfiguration
          (front (recordWithTail o (synchronousPrefix h W z) w1) (P.length+n*L)) (cuts z) ∧
          (cuts z).output.length ≤ k ∧ (cuts z).output = (P.take k).take (cuts z).output.length ∧
          (cuts z).output <+: P.take k ∧
          ReachThrough action initialConfiguration (OperationRecord o b .closed) (P.length+n*L) (cuts z).state) ∧
        Function.Injective (fun z => ((cuts z).state,(cuts z).output)) ∧
        (∀ c, c ∈ states ↔ ∃ z, (cuts z).state = c) ∧
        2^n ≤ states.card*(factor k) ∧
        (∀ B : ℕ, Peak action initialConfiguration (OperationRecord o b .closed) encoding
          (P.length+n*L) ≤ (B : WithTop ℕ) → 2^n ≤ (2^(B+1)-1)*(k+1))) ∧
      (∀ H B : ℕ, P.length ≤ H →
        Peak action initialConfiguration (OperationRecord o b .closed) encoding H ≤ (B : WithTop ℕ) →
        (((H-P.length)/L : ℕ) : ℝ)-1-Real.logb 2 ((k+1 : ℕ) : ℝ) ≤ (B : ℝ)) ∧
      ENNReal.ofReal (1/(L : ℝ)) ≤
        liminf (fun H : ℕ => ENat.toENNReal
          (Peak action initialConfiguration (OperationRecord o b .closed) encoding H)/(H : ENNReal)) atTop ∧
      (∀ a r t vertices H, OperationRecord o b .closed a r →
        Trace action (full r) ⟨initialConfiguration,0,[]⟩ t vertices → t.acquired ≤ H →
        ∀ c ∈ vertices, ((encoding c).length : WithTop ℕ) ≤
          Peak action initialConfiguration (OperationRecord o b .closed) encoding H)


abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ k => k+1) (fun e => nomatch e)

def rejected : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := WholeLaw.{u_1} (r.readout () ())

theorem rejected_law : ¬ sourceArena.{u_1}.Law rejected := by
  intro hypothetical
  have outcome := @hypothetical Reg.Support.FibonacciConsensusUniverse.Configuration.{u_1}
    (Reg.Support.FibonacciConsensusUniverse.action.{u_1} budget)
    Reg.Support.FibonacciConsensusUniverse.initial.{u_1} (fun _ => false) budget
    .G1 .G1 P Q h legal.1 legal.2.1 lengths.1 lengths.2.1
    high low colors 86 (by decide) legal.2.2.1 legal.2.2.2
    lengths.2.2.1 lengths.2.2.2.1 lengths.2.2.2.2 distinct.1 distinct.2 family_budget
    0 first_difference.1 (by intro p hp; omega) first_difference.2
    (Reg.Support.FibonacciConsensusUniverse.safety (fun _ => false) budget budget_bounds.1.le)
    (Reg.Support.FibonacciConsensusUniverse.liveness (fun _ => false) budget budget_bounds.1.le budget_bounds.2)
    (Reg.Support.FibonacciConsensusUniverse.postprocessing (fun _ => false) budget)
    encoding.{u_1} faithful.{u_1}
  obtain ⟨e1,e2,w1,w2,leg1,leg2,in1,out1,in2,out2,tails,families,rest⟩ := outcome
  obtain ⟨cuts,states,actual,align,inj,cutspec,joint,members,count,capacity⟩ := families 0
  norm_num [rejected, realize] at count

def evidence : Registration sourceArena.{u_1}
    (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage.nondegenerate_branch_storage.{u_1}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage.nondegenerate_branch_storage.{u_1},
    rejected, rejected_law⟩
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
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def nondegenerate_branch_storage_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage.nondegenerate_branch_storage.{u_1})
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ k => k+1) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage.NondegenerateOriginal.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage.NondegenerateOriginal.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena.{u_1}⟩
  objectArena := .source ⟨sourceArena.{u_1}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena.{u_1} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ k => k+1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg",
        "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "body",
        "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg",
        "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 27
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms nondegenerate_branch_storage_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage.NondegenerateOriginal
