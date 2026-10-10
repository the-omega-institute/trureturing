import LeanInformationAuditInterface.Contract.Core
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace LeanInformationAudit.Analysis
open D5.S3.ConceptDynamics.InformationEscape
open DependentFamily
universe u t s r o a

/-- The constructor requires the reconstructed type itself, not an equivalence
with a proved proposition. Acquisition also checks the raw compiler telescope,
rigid universe parameters, lexical lets and the selected source occurrences. -/
inductive Reconstruction (original : Sort u) : Sort u → Type u where
  | exact : Reconstruction original original

/-- An author model of the complete original declaration. `occurrence` retains
its original type and universes; callers use the unapplied `@` reference.
`rebuild actual` must reconstruct that type, including all dependent binders.
The selection is a compiler coordinate map, not evidence by itself. -/
structure Source {Statement : Sort u} (occurrence : Statement) where
  signature : Signature.{t,s,r,o,a}
  actual : Realization signature
  rebuild : Realization signature → Sort u
  reconstruction : Reconstruction Statement (rebuild actual)
  selection : Contract.SourceSelection

/-- Reuse ordinary registration operands and their full law, without changing
any ordinary registration obligation or assigning an audit status. -/
def Source.ofRegistration {P : Prop} (occurrence : P)
    {arena : DependentFamily.Arena.{t,s,r,o,a}}
    (registration : DependentFamily.Registration arena P)
    (reconstruction : Reconstruction P (arena.Law registration.actual))
    (selection : Contract.SourceSelection) : Source occurrence where
  signature := arena.signature
  actual := registration.actual
  rebuild := arena.Law
  reconstruction := reconstruction
  selection := selection

/-- All observations, including the total task, belong to the same actual
realization. Repeated or empty additions preserve collapsed layers. The initial
bundle is explicit and need not induce the universal relation. -/
structure Plan {Statement : Sort u} {occurrence : Statement}
    (source : Source.{u,t,s,r,o,a} occurrence) where
  task : source.signature.Role
  initial : List source.signature.Role
  additions : List (List source.signature.Role)

def Plan.selected {Statement : Sort u} {occurrence : Statement}
    {source : Source.{u,t,s,r,o,a} occurrence} (plan : Plan source)
    (position : Nat) : List source.signature.Role :=
  plan.initial ++ (plan.additions.take position).flatten

/-- Qualitative kernels exist without a finite domain, positive information gain
or an acquired probability law. -/
def Plan.kernel {Statement : Sort u} {occurrence : Statement}
    {source : Source.{u,t,s,r,o,a} occurrence} (plan : Plan source)
    (parameter : source.signature.Params) (position : Nat) :
    StructuralKernel (source.signature.State parameter) where
  relation x y := ∀ role ∈ plan.selected position,
    source.actual.readout role parameter x = source.actual.readout role parameter y
  equivalence := ⟨fun _ _ _ => rfl,
    fun h role mem => (h role mem).symm,
    fun h₁ h₂ role mem => (h₁ role mem).trans (h₂ role mem)⟩

/-- Weak refinement includes zero-gain steps, without asking for a strictness witness. -/
theorem Plan.refines {Statement : Sort u} {occurrence : Statement}
    {source : Source.{u,t,s,r,o,a} occurrence} (plan : Plan source)
    (parameter : source.signature.Params) (position : Nat) :
    ∀ x y, (plan.kernel parameter (position + 1)).relation x y →
      (plan.kernel parameter position).relation x y := by
  intro x y h role member
  apply h role
  apply List.mem_append.mpr
  rcases List.mem_append.mp member with initial | added
  · exact Or.inl initial
  · right
    exact List.Sublist.subset
      (List.Sublist.flatten (List.take_sublist_take_left (Nat.le_succ position))) added

end LeanInformationAudit.Analysis
