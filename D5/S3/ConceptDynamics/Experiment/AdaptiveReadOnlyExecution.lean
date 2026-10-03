/- GID: D5/S3/ConceptDynamics/Experiment/AdaptiveReadOnlyExecution
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Experiment/AdaptiveReadOnlyExecution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: History-controlled read-only execution charges distinct queries. -/

import D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization

/-!
Adaptive controllers only read their previous query-response records. Queries
read a fixed source and may have dependent response types. Finite execution has
no fuel or depth bound and imposes no finiteness condition on sources or actions.
Repeated queries are charged once. Stalled and infinite executions have no
finite run witness and therefore have cost infinity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Experiment.AdaptiveReadOnlyExecution

open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist)
open scoped ENNReal

universe u v w z
variable {X : Type u} {A : Type v} {Y : A → Type w} {B : Type z}

/-- A controller reads only the history, choosing a query, a return, or a stall. -/
abbrev Controller (Y : A → Type w) (B : Type z) := Hist Y → Option (A ⊕ B)

/-- Every recorded response agrees with the readout of the same fixed source. -/
def Consistent (read : (a : A) → X → Y a) (h : Hist Y) (x : X) : Prop :=
  ∀ p ∈ h, read p.1 x = p.2

/-- The finite set of distinct query actions recorded in a history. -/
def queries [DecidableEq A] (h : Hist Y) : Finset A :=
  (h.map Sigma.fst).toFinset

/-- Repeating a query contributes no extra charge. -/
def queryCount [DecidableEq A] (h : Hist Y) : Nat := (queries h).card

/-- Finite execution retains the additional ordered record after a prefix.
Only stopping and querying have constructors; stalls and infinite executions
have no finite witness, and finite runs have no uniform depth bound. -/
inductive Run (read : (a : A) → X → Y a) (π : Controller Y B) (x : X) :
    Hist Y → Hist Y → B → Prop
  | stop (pre : Hist Y) (b : B) (decision : π pre = some (.inr b)) :
      Run read π x pre [] b
  | query (pre : Hist Y) (a : A) (t : Hist Y) (b : B)
      (decision : π pre = some (.inl a))
      (next : Run read π x (pre ++ [⟨a, read a x⟩]) t b) :
      Run read π x pre (⟨a, read a x⟩ :: t) b

/-- Every source admits a finite execution returning its target value. -/
def Correct (read : (a : A) → X → Y a) (target : X → B) (π : Controller Y B) : Prop :=
  ∀ x, ∃ t, Run read π x [] t (target x)

/-- The infimum of distinct-query counts over finite execution witnesses.
With no finite witness, including stalls and infinite querying, the cost is top. -/
noncomputable def cost [DecidableEq A] (read : (a : A) → X → Y a)
    (π : Controller Y B) (x : X) : ENNReal :=
  ⨅ t : Hist Y, ⨅ b : B, ⨅ (_ : Run read π x [] t b), (queryCount t : ENNReal)

end D5.S3.ConceptDynamics.Experiment.AdaptiveReadOnlyExecution
