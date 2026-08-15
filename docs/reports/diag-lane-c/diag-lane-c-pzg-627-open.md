# Diagonal Lane C: PZG Remark 6.27 Open Report

Outcome: open, with no formalization deposit.

This is the distinct target for the lane's current round. The atom is not in
the occupied set `{8f0ea7, 2cc156, d7985f, c4dd0c, fb628b, c224075b,
dc712240, 67d2f5, c5c287, 59dcfff7, 8eb0bfb6}`. The earlier report for
`dc712240` remains an independent review and is not counted as this target.

The lane is `harness/diag-lane-c` at
`/Users/mstudio3/trureturing-diag-lane-c`. It fetched and merged
`origin/dev=2a087760bcc2814fa46235252f0c6320122828ad` before selecting this
atom; `git merge-base --is-ancestor origin/dev HEAD` exited `0`. No digestion
ledger, receipt, frozen record, Lean module, or Scribe source was edited.

## Atom and authoritative statement

- Atom ID: `pzg-residual-b9b6b0a69c0a65c6d437b2c9f3983495cd0d52ffbef6fe6a2c4a7f06e1865ba0`
- CAS reference: `sha256:b9b6b0a69c0a65c6d437b2c9f3983495cd0d52ffbef6fe6a2c4a7f06e1865ba0`
- Source: `docs/develop/theory/PZG_BEDC.md`, `remark/6.27`
- `make show-atom ATOM_ID=pzg-residual-b9b6b0a69c0a65c6d437b2c9f3983495cd0d52ffbef6fe6a2c4a7f06e1865ba0`
  exited `0`.
- `show-atom` reported `status=match` for the raw, normalized, and CAS
  SHA-256 values.
- The backfill record names two unresolved subitems:
  `tribonacci-deficit-nonintegrality-and-scan-certificate` and
  `cubic-field-conjugate-trace-explanation`.

The authoritative atom says that a Tribonacci deficit `c_T`, computed using a
Binet main term, is bounded in a scanned range `[-0.955, 0.955]`, is nonintegral
in `44.4%` of cases, and has a discrete nonintegral spectrum. It explains the
contrast with Fibonacci by saying that a quadratic expanding/contracting pair
exhausts all conjugates, while the cubic Tribonacci field has one real and two
complex embeddings, so the isolated main term is not a trace. It concludes
that deficit integrality is a specifically two-sided quadratic privilege.

## Clause-level fidelity analysis

1. **Tribonacci object:** no Tribonacci sequence or characteristic polynomial
   is defined in D5 or pinned Mathlib. Different initial values and index
   conventions produce different Binet coefficients and deficits.
2. **Deficit `c_T`:** the atom does not define which integer is compared with
   which Binet main term, how inputs are encoded, or whether the deficit is a
   one-variable approximation error or a two-input additive coboundary like
   the Fibonacci deficit in theorem 6.22.
3. **Bound `[-0.955, 0.955]`:** the phrase reports the observed output range,
   but gives no input scan window. It therefore cannot be stated as a finite
   certificate, and the atom does not assert a global analytic bound with
   quantified hypotheses.
4. **`44.4%` nonintegral:** no numerator, denominator, sample domain, rounding
   convention, or integrality test is supplied. The decimal alone does not
   determine a proposition.
5. **Discrete spectrum:** no set of values or topology is given. Encoding it
   as finite-valued, discrete in the subspace topology, or merely clustered
   would produce inequivalent statements.
6. **Cubic trace explanation:** a faithful theorem needs the Tribonacci cubic
   polynomial, its three embeddings, an algebraic integer representing the
   exact recurrence term, and an equation separating the real main term from
   the complex conjugate remainder. None of those typed objects exists in the
   source atom or repository.
7. **Quadratic privilege conclusion:** this is presented as a structural
   generality claim. One Tribonacci scan does not prove that all nonquadratic
   encodings lose integrality, and narrowing it to the single scan would drop
   the atom's conclusion.

There is no one-to-one Lean echo. Defining a convenient Tribonacci sequence
and deficit in this lane would choose missing source semantics; proving only
that some computed example is nonintegral would omit the bound, percentage,
discrete-spectrum, trace, and generality clauses.

## Library and duplicate search trace

The following searches were run verbatim:

```text
rg -n -i "Tribonacci|tribonacci|c_T|44\\.4|0\\.955|cubic.*conjug|one real.*two complex|一实二复|三次域" \
  D5 Blueprint --glob '*.lean' --glob '*.md' --glob '*.scribe.cs'
rg -n -i "Tribonacci|tribonacci" \
  .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n -F "pzg-residual-b9b6b0a69c0a65c6d437b2c9f3983495cd0d52ffbef6fe6a2c4a7f06e1865ba0" \
  Meta/Digestion/formalizations docs/reports
```

The results were:

- `D5/S1/Recurrence/CarryCancellation.lean` proves a generic fixed-width
  recurrence carry identity. Its provenance explicitly records that no
  Tribonacci declaration was found. It can accept a future Tribonacci weight
  sequence but does not define one or a Binet deficit.
- `Blueprint/D5/S3/Weil/ReflectionLedger.md` narratively reports that replacing
  Fibonacci by Tribonacci destroys integrality. It supplies no definition,
  scan certificate, or cubic trace theorem, and its own statement distinguishes
  only the compared fixed-point mechanisms.
- Pinned Mathlib had no `Tribonacci`/`tribonacci` declaration.
- No `44.4`, `0.955`, or `c_T` implementation was found in D5 or Blueprint.
- The exact atom ID had no formalization receipt or prior report before this
  file was created.

## Rejected approaches and diagnostics

- **Instantiate the generic carry theorem at width three:** rejected because
  carry preservation is not Binet-deficit nonintegrality and supplies none of
  the numeric certificate.
- **Introduce an arbitrary Tribonacci recurrence and compute one witness:**
  rejected because the atom does not fix initial values, indexing, Binet
  coefficient, deficit, or scan domain.
- **Translate `44.4%` as `444/1000`:** rejected because a reported rounded
  percentage does not identify the actual count or denominator.
- **Translate "discrete spectrum" as a finite set:** rejected because no value
  set or finite scan window is supplied.
- **Prove only that a real cubic root is not a full field trace:** rejected
  because it would omit the relationship to `c_T`, the complex pair, all
  numeric clauses, and the quadratic-privilege conclusion.
- `make show-atom` exited `0` with all hashes matching.
- The repository search exited `0` with 19 hits, none providing the missing
  Tribonacci definition or certificate. The pinned Mathlib search had no hit.

`make deposit`, `make preflight`, `make cover`, and `make emit` were not run.
The workflow stopped at the statement-echo and library-search gates before any
formal artifact was created.

## Fidelity gate and lane state

- **Conclusion substance:** the claimed nonintegrality and trace obstruction
  are substantive, but the source does not determine their formal objects or
  quantifiers.
- **Hypothesis satisfiability/domain inhabitance:** blocked because the
  Tribonacci sequence, Binet main term, deficit domain, and scan window are
  absent.
- **Proof substance:** generic recurrence carry cancellation does not prove the
  stated outcome; installing the outcome in new definitions would be hollow.
- **Duplicate search:** complete for the atom ID and all named numeric,
  Tribonacci, Binet-deficit, and cubic-conjugate terms.
- **Clause fidelity:** blocked; every shortened candidate drops at least the
  numeric certificate, trace explanation, or structural generality claim.
- **Rendered-statement fidelity:** unreached because no Lean/Scribe artifacts
  were created.
- **Grader traps:** the central traps are generic recurrence vs specific Binet
  deficit, rounded percentage vs exact finite certificate, and one cubic
  counterexample vs a universal quadratic-privilege claim.

This is an evidence-complete `open` outcome for the distinct atom. Receipt and
ledger creation remain unreached because no faithful deposit exists.
