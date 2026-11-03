# Finite History Canonical Tree

## Abstract

Pointwise finite termination on a finite candidate set yields one sufficiently unfolded passive tree that preserves every completed query/response history, terminal label, zero-error singleton consequence, and every rational weighted query-count sum.

**Theorem 1.1 (Exact finite-history policy/tree correspondence).**

Let W : Type u, Q : Type, Y : Q → Type, and L : Type. A readout is
read : (q : Q) → W → Y q; a deterministic history policy is
policy : Hist Y → Sum Q L, where the left action queries and the right action
stops with a label. For a finite C : Finset W, assume only

    ∀ x ∈ C, ∃ n t l, execute read policy n [] x = some (t,l).

Then there is N : Nat such that for every n ≥ N, with
tree := boundedTree policy n []:

    ∀ x, (runPassiveProtocol read tree x).length ≤ n

and every successful execution on x ∈ C has exactly the same complete
dependent query/response list as the canonical tree run, the same length and
terminal label, the terminal action is reached at that full history, and its
candidate set is exactly the candidates executing that same complete history and
label at the supplied fuel. For every trace/label assignment that is witnessed
by a successful execution on every candidate and every μ : W → ℚ, the
weighted length sum of the canonical runs equals the weighted length sum of
those original traces. Finally, any decoder decode : L → W that is correct on
all completed candidate runs makes each canonical candidate set a singleton and
makes the canonical transcript injective on C.

The Lean declaration is exactly
D5.S3.ConceptDynamics.Experiment.FiniteHistoryCanonicalTree.finite_history_canonical_tree.
The source also retains the six public supporting declarations
boundedTree_exact, boundedTree_length_le, execute_endpoint,
execute_unique, terminal_candidates, and zero_error_singleton; each is
consumed by the bridge or supplies a directly reusable operational fact.

*Proof.* Machine-checked in the private source listed below. The current assignment
does not recompile or install the source in the canonical repository. ∎

*Source.* Repository-derived from the existing passive-history and dependent-tree
APIs. The exact private source and the inherited HECA receipts are recorded in
the implementation accounting artifact.

## Commentary

Hist Y is the existing dependent list of query/response pairs. The policy
never receives the hidden state; execute reads the same x at every query,
including repeated queries, and records every occurrence. The PassiveProtocol
and runPassiveProtocol carriers and executor are reused verbatim. The
boundedTree operation is the existing operation owned by
D5/S3/Arith/FibonacciAtomic/TerminalGcdAcquisitionCost; its arithmetic
parameters are not part of this theorem.

The common bound is derived from one finite fuel witness for each element of
C and their finite supremum. No common depth is assumed as an input, and no
finiteness is assumed for Q or for any response type Y q. Only actual
candidate runs must terminate. Impossible histories and states outside C need
not terminate. Because boundedTree_exact gives list equality, the result
preserves every query, response, repetition, stop label, and query count; it
does not merely preserve a partition.

terminal_candidates transfers the exact complete-history fibre to the existing
candidates definition. zero_error_singleton turns a universal correct
decoder into a singleton fibre, and the main theorem then gives transcript
injectivity. The rational weights are arbitrary, so this is a pathwise
weighted-count equality rather than a positivity, probability, or
normalization assumption.

For the fixed-support circular-deletion model, specialize
W = Ω(A), Q = A, Y i = Ω(A ∖ {i}), read i C = δᵢ(C), and L = W
with identity decoding. The theorem then supplies the finite canonical-tree
prerequisite for any pointwise terminating zero-error policy. It does not prove
the insertion-gap count, two-deletion fibre classification, third-deletion
separation, or the paper's 2 + 2/(n-1) optimum. The paper remains a separate
paper-proof-only input.

## Interfaces and dependencies

- D5/S3/ConceptDynamics/Experiment/PassiveAdaptiveTranscriptUpperBound
  supplies PassiveProtocol and runPassiveProtocol.
- D5/S3/ConceptDynamics/Experiment/PassivePolicyNormalization supplies
  Hist, execute, execute_mono, execute_transfer, and candidates.
- D5/S3/Arith/FibonacciAtomic/TerminalGcdAcquisitionCost supplies the
  generic boundedTree operation.
- The reverse tree-to-history direction already exists as
  PassivePolicyNormalization.tree_execution; it is not duplicated here.

## Boundaries and admission status

This is an independent policy-semantic prerequisite. It carries no circular
classification or numerical optimum, no bind-only application wrapper, no
finite-branching claim for infinite response alphabets, and no new source API.
The authenticated private HECA compilation is inherited evidence for the exact
source identity only. Canonical installed-source compilation, Scribe compilation,
Reg compilation/admission, and repository gate checks are NOT RUN in this
content-preparation stage.

## References

- Truth anchor: D5/S3/ConceptDynamics/Experiment/FiniteHistoryCanonicalTree.finite_history_canonical_tree
- Dependency: Passive Adaptive Transcript Upper Bound (PassiveAdaptiveTranscriptUpperBound.md)
- Dependency: Passive Policy Normalization (PassivePolicyNormalization.md)
- Consumed operation: D5/S3/Arith/FibonacciAtomic/TerminalGcdAcquisitionCost.boundedTree
