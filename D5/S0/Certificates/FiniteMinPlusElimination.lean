/- GID: D5/S0/Certificates/FiniteMinPlusElimination
   generality: G
   mirror-B: D5/B/S0/Certificates/FiniteMinPlusElimination
   mirror-E: none(waiver:function-lifted-finite-bucket-elimination)
   anchors: []
   utility: none
   digest: Exact finite factor partitions and proved pointwise bucket relaxations preserve complete-assignment lower bounds through executable elimination programs. -/

import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Forall2

/-!
Prepared source, uncompiled. Library search found list permutation sum
invariance, List.Forall₂.sum_le_sum, and the EJM transient pointwise two-factor
merge helper. No reusable stateful bucket-elimination program with offset
accumulation and terminal receipts was found in the finite-certificate or EJM
modules. The existing Mathlib list results are reused below.

Each factor is lifted to a function on an entire assignment. A concrete finite
receipt over remaining axes y and all four eliminated values a supplies the
pointwise bucket inequality by restricting each actual complete assignment.
Scope ordering, axis insertion and local table indexing remain the concrete
application's obligations; no new parallel scope machinery is introduced.
The assignment type may be the subtype of full original events compatible
with one exact prefix, preserving all assignments of that original context.

An operation partitions every active factor occurrence into bucket and rest,
replaces the bucket by a proved lower output, and adds its offset exactly once.
Rest may still depend on the same eliminated axis: this covers mini-bucket
relaxations as well as full bucket elimination. Negative offsets, empty
buckets and constant outputs are allowed when their actual receipts hold.
Terminal receipts bound every remaining factor occurrence using List.Forall₂;
a producer's claimed minimum, optimum or success flag is not a premise.

admission_basis: escape-witness
valid_step_le: proof_shape: content; escape_witness: a literal list partition
and its pointwise bucket inequality prove monotonicity of the computed state.
Consumer: valid_program_le composes this actual next-state transformation.
valid_program_le: proof_shape: content; escape_witness: induction follows the
defined executable run and its validity obligations at every intermediate state.
Consumer: program_lower_bound combines the resulting state with terminal data.
program_lower_bound: proof_shape: content; escape_witness: every terminal
minimum is matched to an actual remaining factor and the resulting threshold
is transported through every program step to the original score invariant.

The intended concrete consumer is the EJM original depth13/code4/index674
finite all-four-values bucket pilot. It must still supply original local
validity, the complete initial 32-factor score bound, every finite receipt and
the original scale conversion 6987435. No original raw Accepted, semantic
prefix bound, root acceptance, complete input or kernel receipt is asserted
by this preparation. First application and compiled source-owned Reg evidence
for the three new public theorems remain unfinished under
https://github.com/the-omega-institute/trureturing/issues/16309
No audit success or declared_validated status is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.FiniteMinPlusElimination

universe u

/-- A scoped table is used through its actual value on a complete assignment. -/
abbrev Factor (Assignment : Type u) := Assignment → ℤ

/-- Every active factor occurrence and the accumulated offset are explicit. -/
structure State (Assignment : Type u) where
  constant : ℤ
  factors : List (Factor Assignment)

/-- The represented lower bound on one complete assignment. -/
def State.value {Assignment : Type u} (state : State Assignment) (e : Assignment) : ℤ :=
  state.constant + (state.factors.map (fun f => f e)).sum

/-- A proposed bucket replacement also supplies the exact untouched list.
An empty kept-axis set is represented by a constant output function. -/
structure Elimination (Assignment : Type u) where
  bucket : List (Factor Assignment)
  rest : List (Factor Assignment)
  offset : ℤ
  output : Factor Assignment

variable {Assignment : Type u}

/-- Execute the proposed replacement and accumulate its offset once. -/
def next (state : State Assignment) (operation : Elimination Assignment) : State Assignment :=
  ⟨state.constant + operation.offset, operation.output :: operation.rest⟩

/-- Partition all active occurrences and prove a lower replacement for every
complete assignment. No exact minimum or axis-independence claim is required. -/
def ValidStep (state : State Assignment) (operation : Elimination Assignment) : Prop :=
  state.factors.Perm (operation.bucket ++ operation.rest) ∧
    ∀ e, operation.offset + operation.output e ≤
      (operation.bucket.map (fun f => f e)).sum

/-- Execute every operation in order, using its actual preceding state. -/
def run : State Assignment → List (Elimination Assignment) → State Assignment
  | state, [] => state
  | state, operation :: operations => run (next state operation) operations

/-- Every operation must be valid on the state actually computed before it. -/
def ValidProgram : State Assignment → List (Elimination Assignment) → Prop
  | _, [] => True
  | state, operation :: operations =>
    ValidStep state operation ∧ ValidProgram (next state operation) operations

/-- Match one proved lower minimum to every remaining factor occurrence,
then check the desired threshold against the accumulated constant and sum. -/
def Terminal (state : State Assignment) (gap : ℤ) : Prop :=
  ∃ minima : List ℤ,
    List.Forall₂ (fun m f => ∀ e, m ≤ f e) minima state.factors ∧
      gap ≤ state.constant + minima.sum

/-- A valid bucket relaxation decreases the represented lower-bound function
on every original complete assignment, including every eliminated value. -/
theorem valid_step_le (state : State Assignment) (operation : Elimination Assignment)
    (valid : ValidStep state operation) :
    ∀ e, (next state operation).value e ≤ state.value e := by
  rcases valid with ⟨partition, receipt⟩
  intro e
  have sums : (state.factors.map (fun f => f e)).sum =
      (operation.bucket.map (fun f => f e)).sum +
        (operation.rest.map (fun f => f e)).sum := by
    simpa only [List.map_append, List.sum_append] using
      (partition.map (fun f : Factor Assignment => f e)).sum_eq
  calc
    (next state operation).value e =
        state.constant + (operation.offset + operation.output e) +
          (operation.rest.map (fun f => f e)).sum := by
      simp only [next, State.value, List.map_cons, List.sum_cons, add_assoc]
    _ ≤ state.constant + (operation.bucket.map (fun f => f e)).sum +
          (operation.rest.map (fun f => f e)).sum :=
      add_le_add (add_le_add le_rfl (receipt e)) le_rfl
    _ = state.value e := by
      simp only [State.value, sums, add_assoc]

/-- Any finite valid program preserves the complete-assignment lower-bound
invariant by following the actual next states, without recomputing minima. -/
theorem valid_program_le (initial : State Assignment)
    (operations : List (Elimination Assignment)) (valid : ValidProgram initial operations) :
    ∀ e, (run initial operations).value e ≤ initial.value e := by
  induction operations generalizing initial with
  | nil =>
    intro e
    exact le_rfl
  | cons operation operations ih =>
    intro e
    exact (ih (next initial operation) valid.2 e).trans
      (valid_step_le initial operation valid.1 e)

private theorem terminal_le (state : State Assignment) (gap : ℤ)
    (terminal : Terminal state gap) : ∀ e, gap ≤ state.value e := by
  rcases terminal with ⟨minima, bounds, threshold⟩
  intro e
  have pointwise : List.Forall₂ (fun (m : ℤ) (f : Factor Assignment) => m ≤ f e)
      minima state.factors :=
    List.Forall₂.imp (fun _ _ lower => lower e) bounds
  have mapped : List.Forall₂ (· ≤ ·) minima (state.factors.map (fun f => f e)) :=
    List.forall₂_map_right_iff.mpr pointwise
  exact threshold.trans (add_le_add le_rfl mapped.sum_le_sum)

/-- A complete valid program and terminal receipts imply the threshold for
the original score. Initial factor coverage and score soundness stay explicit. -/
theorem program_lower_bound (score : Assignment → ℤ) (initial : State Assignment)
    (operations : List (Elimination Assignment)) (gap : ℤ)
    (initialLower : ∀ e, initial.value e ≤ score e)
    (valid : ValidProgram initial operations)
    (terminal : Terminal (run initial operations) gap) :
    ∀ e, gap ≤ score e := by
  intro e
  exact (terminal_le (run initial operations) gap terminal e).trans
    ((valid_program_le initial operations valid e).trans (initialLower e))

#print axioms valid_step_le
#print axioms valid_program_le
#print axioms program_lower_bound
end D5.S0.Certificates.FiniteMinPlusElimination
