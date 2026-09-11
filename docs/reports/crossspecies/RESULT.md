# Conditional cross-species consensus

**Implementation outcome: 成**, under the caller's local build-and-gates criterion.
This does not mean the physical inputs were adopted or that a PR was merged.

Origin: Codex implementation worker using the lean4 skill, one implementation thread.
No independent review or multi-model consensus is claimed. The caller owns later
review and merge stages. Preregistration precedes Lean source in commit `8b07c89ace`.

## Mathematical result and its boundary

For a group representation U by finite complex matrices, assume explicitly that
`matrixRepresentation U` is irreducible (`h_irreducible`). For a Hermitian matrix A
(`h_selfAdjoint`), assume `h_equivariant : ∀ g, A * U g = U g * A`.
Then there is a real r with A = (r : ℂ) • I.

For every species-indexed family of probe matrices with trace one (`h_normalized`),
the same theorem gives a single r with Re tr(probe(s) A) = r for every species,
and hence equality of every pair of readings. This companion theorem actually
consumes the scalar theorem; the representation and observable are shared arguments,
not unrelated pieces of infrastructure.

This is a **conditional theorem**, a tier-3 formal terrain map. It does not establish
that all probes carry the same active symmetry or that this symmetry acts
irreducibly. Those are precisely the physical inputs still unadopted in
`docs/reports/quantum-reality/OPEN-QUESTIONS.md`. The complex field and finite dimension
specify this scope. Physical density matrices are included, although trace-one
normalization alone suffices. Unitarity is not needed for this implication. Consensus
uses one common observable and calibration, not independently chosen observables.

## Shape, provenance, and utility

All GIDs below share the prefix `D5/S3/Quantum/Matrix/CrossSpeciesConsensus.`.

| Declaration | proof_shape | admission_basis | escape_witness | Direct frozen dependencies |
| --- | --- | --- | --- | --- |
| equivariant_selfAdjoint_eq_smul_id_of_irreducible | bind-only | rule-11-upstream-wrapper | none | [] |
| cross_species_consensus | bind-only | rule-11-upstream-wrapper, companion | none | [] |

The first row is the main wrapper. The second fulfills the preregistered
consensus obligation; direction: `cross_species_consensus` ->
`equivariant_selfAdjoint_eq_smul_id_of_irreducible` -> Mathlib Schur. This module
is frozen as one unit, not as independent deposits for each consequence.
`matrixRepresentation` is a definition transporting U via an existing algebra equivalence.
The two generated `_proof_1`/`_proof_2` theorems are its map-law proof fields.

The actual Schur dependency is the more direct pinned-library hit
`Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed`.
`CategoryTheory.endomorphism_simple_eq_smul_id` and `FDRep.finrank_hom_simple_simple`
were read first; the unbundled API avoids an unnecessary category bridge. The matrix
transport, scalar restriction by Hermitian diagonal entries, and normalized trace
calculation are applications/projections/normalizations of upstream results. No new
escape witness is claimed. The proposed classification did not change.

The full search receipt and concrete repository API need are in
[preregistration-v1.md](preregistration-v1.md). The pinned upstream source was also
opened via its immutable GitHub raw URL: HTTP 200, 3720 bytes. Pin:
`db584cd6d46c92f209a44c0f1c829460d327499d` (Lean 4.33.0).
The Library note contains both locator keys with only URL non-null, and repeats the
exact bound URL in its Verified locator section. No theory volume or atom was created.

`utility: none`: the definition, both general theorems, and generated map-law proofs
are not bounded enumerations, checkers, numeric reductions, or certified finite
instances. Other computational utility fields are not-applicable(kind=none).
The floating-point experiment below remains a diagnostic, outside D5.

## Numerical control, recomputed

Reproduce with `python3 docs/reports/crossspecies/commutant_probe.py`.
Seed 20260911; NumPy 2.0.2; complex matrices; dimensions 2–8 repeated across 30 cases.
Each generic case uses two independent Gaussian-QR unitary generators. The matched
reducible case uses two independently generated block-diagonal unitaries with
block sizes floor(n/2), n-floor(n/2).

For column-vectorization, the stacked constraint matrix has blocks
`g.T ⊗ I - I ⊗ g`. Nullity counts singular values at most `1e-10 * largest`.
All 30 generic nullities are 1; all 30 reducible nullities are 2. Across both groups,
the smallest retained singular value is 0.38289912661674774 and the largest null
singular value is 7.917140675208769e-16. Full per-case diagnostics are in
[commutant_probe.json](commutant_probe.json).

These measurements confirm the predicted discrimination in this finite numerical
sample. They do not establish irreducibility in Lean, a universal random-matrix
claim, or either missing physical input.

## Kernel and local gate receipts

The first prescribed serial build completed 12 missing units with failed=0. After the compiler
recommended `have` in place of `haveI`, only this new module's own generated olean
was removed to let the existence-based serial driver rebuild the changed source.
The final source build emitted:

```text
SERIAL_LEAN status=complete built=1 failed=0 missing=1 tree=/Users/chronoai/trureturing-a392714bridge
```

`make lean-report`: exit 0, delta changed=0 added=1 removed=0 recheck=1. Its source-bound
report lists only `Classical.choice`, `Quot.sound`, `propext` for **all five declarations**,
including generated map-law fields. There is no `sorryAx` or private axiom. The source
has zero occurrences of `axiom`, `instance`, `sorry`, `native_decide`, or `rfl`;
77 lines, maximum width 97. The public hypotheses retain the explicitly named
`h_irreducible` parameter; the local `have` only passes that supplied proof upstream.

Statement IDs from the canonical inspector:

- matrixRepresentation: `sha256:3f8622a31c0ae33105bcb622705485503f5049c7e71a23b604ad140fc9ea0a3e`
- scalar theorem: `sha256:9bb08c3676f60db283c08f3de88d4f2895869debd96852d014f230448f0a4114`
- consensus theorem: `sha256:36a89f748c3b41e367f15c2c71abc84dad95e2fa00efeeb7e3d9d9792d2b0120`

## Failed attempts

The router initially rejected an absolute manifest path and then null optional fields.
Reading its contract resolved these as a repository-relative manifest with string
fields; routing returned the canonical Quantum/Matrix path and seven-line skeleton.
No Lean proof attempt failed. The first `make emit` failed on a formula identifier
containing an underscore. The first repair used a nonexistent `Sub` constructor,
which C# compilation rejected. Reading the full DSL resolved the cause: express
the family as the existing `Call("probe", Id("s"))` function-application form.
No validation or detection was weakened.

## Completed gate chain

The validated chain is serial Lean build -> `make lean-report` -> `make emit`
-> `make deposit-uncovered`. The final emission exited 0 and produced one Blueprint.
The deposit command also exited 0; its own ordered report, header check, emission,
and ledger writer all succeeded. No atom coverage was requested or written.

```text
DEPOSIT_HEADER_CHECKED SL-012 D5/S3/Quantum/Matrix/CrossSpeciesConsensus.lean
LEDGER_ALIGN selectors_considered=4046 changed=0 added=1 unchanged=4045 conflicts=0
```

Deposit anchor:
`D5/S3/Quantum/Matrix/CrossSpeciesConsensus.equivariant_selfAdjoint_eq_smul_id_of_irreducible`.
Module pin: `sha256:672f7703c7fa0dadde253054bfab3473c762e4dc1bd2e354f6dcd25bdf3fc386`.
Freeze event: `sha256:30f7ae44c291fc072bd99bd31ce825480bf76ad1cb4387a38056b55efafcded0`.

The exact-merge-base CI-layer command exited 0, with base
`0959718b31ddd1d663683c2d71ac23c32ccb6e8d`:

```text
DESCRIBE_STATUS case=DESCRIBE-NODES status=classified nodes=11107 suspected_novel=0 formula_content_slots=68 formula_statements=32 red=0 observe=4997
markdown: judged=1 formula(s)=2 red=0
```

There were zero lines beginning `RED`. No OPEN projection or OBSERVE line was used
as a green verdict. `git diff --check` also exited 0. Final immediate file counts:
D5 matrix 6, Blueprint matrix 6 (generated .md excluded), Library Quantum 20,
crossspecies reports 4. Domain and generality checks retain the preregistered result.

Remote dev was fetched to `d0070d656d`; `git merge-tree --write-tree HEAD origin/dev`
exited 0 with no conflicts. The second D5 exact-name search on that dev revision
found neither new theorem. This is a bounded duplicate search, not global novelty.

Raw logs, the selected source-bound Lean report, and upstream source receipt are in:
`/var/folders/wv/ht3wzsj138b4sxl3q4t0xdr40000gn/T/consensus-rnd/sshx/crossspecies-1/attempt-1/`.
Relevant logs are `serial-lean-2.log`, `lean-report.log`, `emit-3.log`, `deposit.log`,
and `scribe-content-checks.log`. Earlier failures remain in `emit-1.log` and `emit-2.log`.
PR and final commit identities are recorded in the runner result envelope.
