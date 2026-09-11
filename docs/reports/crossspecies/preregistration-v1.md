# Cross-species conditional slice: preregistration v1

Origin: Codex implementation worker, lean4 skill, single implementation thread;
no independent review or multi-model consensus is claimed. This is the implementation
stage assigned by the caller, not the review or merge stage.

## Scope and classification, before Lean implementation

Tier 3: a formal terrain map for quantum-reality #6298. Schur's lemma is known.
This module does not select or assert new physical axioms. The missing input in
`docs/reports/quantum-reality/OPEN-QUESTIONS.md` is that probes carry the same active
symmetry and that its representation is irreducible. Both remain conditional inputs.

Proposed `proof_shape: bind-only`, `admission_basis: rule-11-upstream-wrapper`,
`escape_witness: none`. No claim of a new proof of Schur's lemma.

Interface: any group G and a finite complex matrix representation U. The explicitly
named argument `h_irreducible` asserts `Representation.IsIrreducible` of the induced
linear representation. The observable A is Hermitian and the explicitly named
`h_equivariant` says A commutes with U(g) for every g. Conclude A = r times identity
for some real r. A companion consensus theorem uses the very same U and A for every
species and proves equality of the real trace readings of arbitrary trace-one probe
matrices. Positivity is unnecessary for this algebraic conclusion; physical density
matrices are included. Unitarity is likewise unnecessary once irreducibility is given.
Finite dimension and the complex scalar field are explicit scope restrictions.

Planned public declarations in `D5/S3/Quantum/Matrix/CrossSpeciesConsensus`:

- `matrixRepresentation`: transport a matrix action through `Matrix.toLinAlgEquiv'`.
- `equivariant_selfAdjoint_eq_smul_id_of_irreducible`: the scalar theorem above.
- `cross_species_consensus`: equality of normalized trace readings, consuming the
  scalar theorem. Direction: consensus -> scalar theorem -> upstream Schur.

Concrete repository need: `Quantum` is registered as finite-dimensional complex
operator algebra and probability. `Matrix/MatrixSelfPairing.lean` consumes concrete
complex matrices with trace-one weights; `Divergence/QuantumRelativeEntropyDefectComposition`
defines density states by positivity and trace one. The proposed slice named in
OPEN-QUESTIONS has no D5 declaration. A concrete commuting-matrix interface plus the
normalized trace corollary connects these existing APIs to the upstream theorem.
No D5 imports are planned, hence direct frozen dependencies are [] for each declaration.

All declarations are general mathematical definitions/theorems, not bounded enumeration,
checkers, numeric reductions, or certified finite instances: `utility: none`.
Other utility fields: not-applicable(kind=none).

## Search receipt

Ordered search used local rg to locate declarations, followed by reading their source;
elaboration will verify the exact application and resulting axiom closure.

1. D5: exact `equivariant_selfAdjoint_eq_smul_id_of_irreducible` and `cross.species`:
   no target hit. `OrthogonalRecordEntropy` found as a conditional-result example.
   `SchurMinimum` is a Schur complement result, not representation-theoretic Schur.
2. Pinned Mathlib: read all of `CategoryTheory/Preadditive/Schur.lean` and
   `RepresentationTheory/FDRep.lean`. Exact categorical hit:
   `CategoryTheory.endomorphism_simple_eq_smul_id`: over an algebraically closed field,
   Simple X and finite-dimensional End(X) imply every endomorphism is scalar identity.
3. Follow-up in `RepresentationTheory/Irreducible.lean` found the more direct hit
   `Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed`.
   It gives bijectivity of scalar inclusion into intertwining endomorphisms for any
   finite-dimensional irreducible representation over an algebraically closed field.
   Prefer this existing unbundled Schur API to constructing a categorical bridge.
   `IsIrreducible` means the subrepresentation order is simple (nontrivial, no proper
   nontrivial invariant subspace), not a postulated scalar-commutant conclusion.
4. Concrete transports: `Matrix.toLinAlgEquiv'`, `Complex.conj_eq_iff_real`, and
   Hermitian diagonal entries. These are normalization of the Schur output.
5. No third-party dependency is needed after the exact pinned-library hit. Public
   upstream locator and pin will be verified and recorded with the Library note.

## Checks and stopping rule

Before additions, immediate file counts are D5 matrix 5, Blueprint matrix 5
(generated .md excluded), Library Quantum 19, reports crossspecies 0; upper bound 48.
Domain Quantum is registered at S3; G imports only Mathlib.

Numerical diagnostic preregistration: seeded complex Gaussian QR, two unitary
generators; 30 generic cases versus 30 matching block-diagonal cases. Compute complex
commutant nullity from the stacked Kronecker commutator, record dimension, seed,
tolerance and singular-value diagnostics. Predict nullity 1 versus >1. This is
floating-point diagnostic evidence only and never a kernel proof of irreducibility.

Success (caller definition): substantive conditional theorem and consensus corollary,
no sorry/private axiom, serial build complete failed=0, lean-report exit 0, emit,
deposit-uncovered, and the exact-merge-base Scribe CI check. Refutation requires a
kernel witness. Otherwise hand back proved partial results and sharp blockers.
Any changed proof shape or needed new bridge requires a new preregistration before
its implementation. Commit each compilable unit immediately. No theory ingestion.
