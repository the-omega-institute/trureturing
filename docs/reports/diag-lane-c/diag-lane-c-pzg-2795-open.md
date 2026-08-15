# Diagonal Lane C: PZG Remark 27.95 Open Report

Outcome: open, with no formalization deposit.

The lane is `harness/diag-lane-c` in
`/Users/mstudio3/trureturing-diag-lane-c`. Before candidate selection it
fetched and merged `origin/dev=600528ed47fd08001838b5db51de4bb71f12936e`;
`git merge-base --is-ancestor origin/dev HEAD` exited `0`. This report is the
only intended change after that synchronization. No digestion ledger,
formalization receipt, frozen record, Lean module, or Scribe source was edited.

## Atom and authoritative statement

- Atom ID: `pzg-residual-dc71224083fd410013c0148478a38aede8e0bd4e62827aa1e5a4fcd7eec37333`
- CAS reference: `sha256:dc71224083fd410013c0148478a38aede8e0bd4e62827aa1e5a4fcd7eec37333`
- Source: `docs/develop/theory/PZG_BEDC.md`, `remark/27.95`
- `make show-atom ATOM_ID=pzg-residual-dc71224083fd410013c0148478a38aede8e0bd4e62827aa1e5a4fcd7eec37333`
  exited `0`.
- `show-atom` reported `status=match` for raw, normalized, and CAS SHA-256
  values.
- The backfill record lists three unresolved subitems: the `2.3e-6` minimum
  distance certificate, the epsilon `1e-4` first-return-at-`6765`
  certificate, and exact nonrecurrence/Fibonacci-return claims.

The authoritative atom divides an interpretation of eternal recurrence into
three clauses. Its mathematical clause says that the golden rotation never
returns exactly because the golden ratio is irrational, reports a minimum
distance `2.3e-6`, and reports that for epsilon `1e-4` the first return is
`k=6765`. Its second clause classifies approximate recurrence and
self-similarity as a mathematical metaphor. Its third clause places an
ethical imperative outside the mathematical ledger.

## Clause-level fidelity analysis

1. **Exact nonrecurrence:** this has a faithful mathematical core. With
   `d(k) = dist (k * phi) Z`, irrationality gives `d(k) != 0` for every
   positive natural `k`. Neighboring D5 declarations already prove the
   needed irrational-multiple and golden-word aperiodicity mechanisms.
2. **Minimum `2.3e-6`:** the source supplies no search interval. Over all
   positive integers there is no positive minimum: irrational rotation has
   arbitrarily close returns, while irrationality prevents distance zero.
   Thus the literal global reading is false, and a finite-scan reading needs
   a missing upper bound. Choosing one would fabricate a source hypothesis.
3. **First epsilon return `6765`:** a faithful finite statement needs an
   explicit distance convention and quantifiers, for example distance to the
   nearest integer, strict `< 1/10000` at `6765`, and `>= 1/10000` for every
   positive `k < 6765`. The atom does not state those conventions. Existing
   first-return modules concern returns to rotation-gap arcs and do not imply
   this numeric threshold certificate.
4. **"Only at Fibonacci scale":** this is a generality claim, not just the
   single `6765` check. It needs a quantified sequence of thresholds or a
   best-approximation theorem; neither is specified in the atom.
5. **Metaphor and ethical boundary:** these are semantic classifications, not
   propositions with stated formal domains. Dropping them would fail the
   one-atom clause map; encoding them as arbitrary predicates would install
   the conclusion by definition.

The exact nonrecurrence clause alone is therefore too narrow to cover this
atom. The numeric minimum is under-specified and false under its unbounded
literal reading, while the finite certificate and general Fibonacci-scale
claim require definitions and quantifiers not present in the source.

## Library and duplicate search trace

The repository and pinned Mathlib were searched with:

```text
rg -n -i "6765|golden rotation|rotation.*return|first return|irrational.*golden|three distance|Morse.Hedlund|aperiodic|quasiperiodic" \
  D5 Blueprint --glob '*.lean' --glob '*.md' --glob '*.scribe.cs'
rg -n -i "goldenRatio.*irrational|irrational.*goldenRatio|6765|first return" \
  .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n -F "pzg-residual-dc71224083fd410013c0148478a38aede8e0bd4e62827aa1e5a4fcd7eec37333" \
  Meta/Digestion/formalizations docs/devloop/reports
```

Relevant hits were:

- `D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore.lean` proves that a
  positive multiple of an irrational rotation has nonzero fractional part
  and develops general interval-return machinery.
- `D5/S1/Words/ReturnWords/GoldenArcFirstReturn.lean` proves that golden
  rotation-gap arcs have exactly two positive first-return times. It does not
  state the nearest-integer epsilon return at `6765`.
- `D5/S1/Words/Complexity/MechanicalComplexityCharacterization.lean` and
  `D5/S1/Words/Mechanical/MechanicalPeriodicity.lean` cover irrationality,
  exact factor complexity, and nonperiodicity.
- `D5/S1/Phase/ThreeDistance.lean` covers the at-most-three adjacent-gap
  theorem, not the claimed finite numeric scan.
- Mathlib supplies `Real.goldenRatio_irrational`.

No occurrence of `6765` or `1/10000` implementing this certificate was found
in D5 or Blueprint. The exact atom search found no formalization receipt or
earlier report before this file was created.

## Rejected approaches and machine diagnostics

- **Deposit exact nonrecurrence alone:** rejected because it drops the two
  numeric certificate clauses, the Fibonacci-scale generality claim, and the
  two semantic clauses.
- **Interpret `2.3e-6` as a global minimum:** rejected because density gives
  arbitrarily small positive returns, so no such positive global minimum
  exists.
- **Invent a finite scan bound:** rejected because the source does not name
  one; different bounds produce different propositions.
- **Define "Fibonacci scale" to mean only `6765`:** rejected as a
  mechanism/outcome mismatch and an unjustified weakening of a plural/general
  claim.
- **Formalize the semantic and ethical verdicts by new definitions:** rejected
  as definitional tautology rather than proof substance.
- `make lean-report` exited `0` after producing the canonical raw Lean report;
  this was needed because the run-local residual producer initially exited
  `2` with `DIGEST_STATUS_INVALID` when that report was absent.
- `make show-atom` exited `0` with matching hashes.

`make deposit`, `make preflight`, `make cover`, and `make emit` were not run.
The task stopped at the statement-echo fidelity gate, before artifact creation.

## Fidelity gate and lane state

- **Conclusion substance:** the nonrecurrence and finite first-return clauses
  are substantive, but the atom does not determine one complete Lean
  conclusion.
- **Hypothesis satisfiability/domain inhabitance:** unreached for a deposit;
  the missing scan bound and distance convention prevent a unique statement.
- **Proof substance:** exact nonrecurrence can reuse irrationality, but that
  proof does not discharge the numeric or generality clauses.
- **Duplicate search:** complete for the atom ID, `6765`, epsilon-return,
  golden-rotation, first-return, irrationality, and aperiodicity terms.
- **Clause fidelity:** blocked by the unspecified numeric window/convention and
  the semantic clauses. The dropped-or-invented clause set cannot be empty.
- **Rendered-statement fidelity:** unreached because no Lean or Scribe artifact
  was created.
- **Grader traps:** the central traps are finite-vs-global minimum,
  single-certificate-vs-Fibonacci-family generality, and mathematical
  proposition-vs-semantic classification.

This is an evidence-complete `open` outcome. Ledger rebinding and receipt
creation remain outside this lane because there is no faithful deposit.
