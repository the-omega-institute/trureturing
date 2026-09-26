import D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization
import Reg.Support.DependentFamily

noncomputable section
namespace Reg.D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization

open _root_.D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v w z

/-- All source coordinates preceding the state, with the original dependent types. -/
abbrev Parameters := Σ (W : Type u), Σ (Q : Type v), Σ (Y : Q → Type w),
  Σ (L : Type z), Σ (_ : (q : Q) → W → Y q), Σ (_ : Hist Y → Sum Q L),
  Σ (_ : ℕ), Hist Y

def signature : Signature where
  Params := Parameters.{u, v, w, z}
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Option (Hist p.2.2.1 × p.2.2.2.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def executionReadout (p : Parameters.{u, v, w, z}) : signature.State p → signature.Output () p :=
  execute p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2

def actual : Realization signature.{u, v, w, z} :=
  realize signature (fun _ => executionReadout) (fun e => nomatch e)

/-- The complete source law, varying only the selected execution observation. -/
def executionLaw (r : Realization signature.{u, v, w, z}) : Prop :=
  ∀ {W : Type u} {Q : Type v} {Y : Q → Type w} {L : Type z}
    (read : (q : Q) → W → Y q) (policy : Hist Y → Sum Q L),
    ∀ n h x t l, r.readout () ⟨W, Q, Y, L, read, policy, n, h⟩ x = some (t, l) →
      (∀ a ∈ t, read a.1 x = a.2) ∧
      ∀ y, (∀ a ∈ t, read a.1 y = a.2) →
        r.readout () ⟨W, Q, Y, L, read, policy, n, h⟩ y = some (t, l)

def arena : Arena where
  signature := signature.{u, v, w, z}
  Law := executionLaw

abbrev TargetW := ULift.{u} Bool
abbrev TargetQ := ULift.{v} Unit
abbrev TargetY (_ : TargetQ.{v}) := ULift.{w} Bool
abbrev TargetL := ULift.{z} Unit

def targetRead (_ : TargetQ.{v}) (x : TargetW.{u}) : TargetY.{v, w} ⟨()⟩ :=
  ⟨x.down⟩

def targetPolicy (h : Hist TargetY.{v, w}) : Sum TargetQ.{v} TargetL.{z} :=
  match h with
  | [] => .inl ⟨()⟩
  | _ :: _ => .inr ⟨()⟩

def targetParameters : Parameters.{u, v, w, z} :=
  ⟨TargetW, TargetQ, TargetY, TargetL, targetRead, targetPolicy, 2, []⟩

/-- A whole-family intervention; every other parameter fiber stays actual. -/
def rejectedReadout : ∀ p : Parameters.{u, v, w, z}, signature.State p → signature.Output () p := by
  classical
  exact Function.update (actual.readout ()) targetParameters
    (fun _ => some ([⟨⟨()⟩, ⟨false⟩⟩], ⟨()⟩))

def rejected : Realization signature.{u, v, w, z} :=
  realize signature (fun _ => rejectedReadout) (fun e => nomatch e)

theorem rejected_law : ¬ arena.{u, v, w, z}.Law rejected := by
  classical
  intro law
  have completed : rejected.readout () targetParameters.{u, v, w, z} (⟨true⟩ : TargetW.{u}) =
      some ([⟨⟨()⟩, ⟨false⟩⟩], (⟨()⟩ : TargetL.{z})) := by
    exact congrFun (Function.update_self targetParameters.{u, v, w, z}
      (fun _ => some ([⟨⟨()⟩, ⟨false⟩⟩], ⟨()⟩)) (actual.readout ())) ⟨true⟩
  have truth := (law targetRead targetPolicy 2 [] (⟨true⟩ : TargetW.{u})
    [⟨⟨()⟩, ⟨false⟩⟩] (⟨()⟩ : TargetL.{z}) completed).1
  have impossible := truth ⟨⟨()⟩, ⟨false⟩⟩ (List.mem_cons_self ..)
  cases impossible

/-- The statement is the complete original theorem; no fiber is removed. -/
def registration : Registration arena.{u, v, w, z}
    (∀ {W : Type u} {Q : Type v} {Y : Q → Type w} {L : Type z}
      (read : (q : Q) → W → Y q) (policy : Hist Y → Sum Q L),
      ∀ n h x t l, execute read policy n h x = some (t, l) →
        (∀ a ∈ t, read a.1 x = a.2) ∧
        ∀ y, (∀ a ∈ t, read a.1 y = a.2) →
          execute read policy n h y = some (t, l)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@execute_trace_transfer.{u, v, w, z}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j different
      exact (different (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro role
    refine ⟨targetParameters, (⟨false⟩ : TargetW.{u}), (⟨true⟩ : TargetW.{u}), ?_⟩
    change execute targetRead targetPolicy 2 [] (⟨false⟩ : TargetW.{u}) ≠
      execute targetRead targetPolicy 2 [] (⟨true⟩ : TargetW.{u})
    simp [execute, targetPolicy, targetRead]

register_information_theorem execute_trace_transfer in arena
  readout via (realize signature.{u, v, w, z}
    (fun _ => executionReadout) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization
    coordinates := #[0, 1, 2, 3, 4, 5, 6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 8 }] })
  escape continues (open)

end Reg.D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization
