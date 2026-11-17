import LeanInformationAuditInterface.Contract.Analysis.Source
import D5.S3.ConceptDynamics.Interventions.DynamicClosureMinimality

namespace LeanInformationAudit.Analysis
open D5.S3.ConceptDynamics.Interventions.DynamicClosureMinimality
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

/-- A mathematical operation model. Source correspondence is a separate,
compiled obligation of the owning adapter; a model alone certifies no source. -/
structure PredictionModel (State Input Summary Reply : Type*) where
  observe : State → Summary
  step : Input → State → State
  reply : State → Reply
  decode : Summary → Reply
  reply_eq : ∀ state, reply state = decode (observe state)

/-- Closure quantifies over every state pair and every declared input. -/
def PredictionModel.Closed {State Input Summary Reply : Type*}
    (model : PredictionModel State Input Summary Reply) : Prop :=
  InterventionClosed model.observe model.step

/-- Reuse the existing least dynamic refinement: one-step closure certifies
complete reply agreement after every finite word of the declared inputs. -/
theorem PredictionModel.future_of_closed {State Input Summary Reply : Type*}
    (model : PredictionModel State Input Summary Reply) (closed : model.Closed)
    {left right : State} (same : model.observe left = model.observe right)
    (word : List Input) :
    model.reply (runWord model.step word left) =
      model.reply (runWord model.step word right) := by
  have refinement : D5.S3.ConceptDynamics.ConceptJoinUniversal.Refines
      model.reply model.observe := ⟨model.decode, funext model.reply_eq⟩
  obtain ⟨factor, factors⟩ := dynamic_closure_is_least
    model.reply model.step model.observe refinement closed
  have equal : DynClosure model.reply model.step left =
      DynClosure model.reply model.step right := by
    rw [factors]
    exact congrArg factor same
  exact congrFun equal word

/-- The ordinary plan's actual selected observations can be used directly as
an operation model's summary. This retains the original source and parameter;
finite roles imply no finiteness of its state or output families. -/
def Plan.observation {Statement : Sort u} {occurrence : Statement}
    {source : Source.{u,t,s,r,o,a} occurrence} (plan : Plan source)
    (parameter : source.signature.Params) (position : Nat)
    (state : source.signature.State parameter) :
    (role : {r // r ∈ plan.selected position}) → source.signature.Output role.val parameter :=
  fun role => source.actual.readout role.val parameter state

/-- Equality of the actual summary is exactly the existing structural kernel. -/
theorem Plan.observation_eq_iff {Statement : Sort u} {occurrence : Statement}
    {source : Source.{u,t,s,r,o,a} occurrence} (plan : Plan source)
    (parameter : source.signature.Params) (position : Nat)
    (left right : source.signature.State parameter) :
    plan.observation parameter position left = plan.observation parameter position right ↔
      (plan.kernel parameter position).relation left right := by
  constructor
  · intro same role member
    exact congrFun same ⟨role, member⟩
  · intro same
    funext role
    exact same role.val role.property

end LeanInformationAudit.Analysis
