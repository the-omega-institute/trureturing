---
slug: oeis-a393867-all-terms-odd
bibkey: hanna2026a393867
doi: null
url: https://oeis.org/A393867
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative
---

# A393867: every logarithmic-derivative coefficient is odd

## Problem

The second OEIS A393867 comment is exactly: "Conjecture: all terms are odd."
The target is `Odd (a393867 n)` for every `n >= 1`, using the definition in
`PrimePowerShiftLogDerivative`. This is the first-tier 2026 conjecture; the
prime-divisibility comment and A393866's shifted printed formula are distinct.

## Motivation

Resolve the second 2026 OEIS conjecture by a universal theorem, extending the
frozen source construction without changing its definitions or statements.

### Implementation record

Skill context: `lean4`; Codex implementation worker, single source of reasoning,
zero independent review seats in this worker. User-supplied numerical claims
were independently rerun here. No multi-model consensus is claimed.
Base: `6af98a19b1fd4f76f1bc1bf92b61593a0c167a09`.
The existing frozen Lean module is read-only. The parity directory contains
26 files before this change (`find D5/S1/Recurrence/Parity -type f | wc -l`).

## Route

Proposed escape witness: the paired-coefficient theorem
`F_(2m) = F_(2m+1)` modulo two, derived from the integral source equations.
Implementation form: over `ZMod 2`, set `D = (1+X)*F' - F`. Its odd-degree
coefficients vanish identically. At even degree `k > 0`, take the defining
equation at `n=k+1`; the prime is odd, so the power rule turns this equation
into `coeff k (D * F^(prime n - 1)) = 0`. Strong induction and the constant
coefficient one force `coeff k D = 0`. The base uses the integral equation at
`n=1`, which gives `F_1=1` before reducing modulo two. Thus `D=0` proves the
paired-coefficient witness. Multiplying by the unit inverse of F then gives
`(1+X)*(F'/F)=1`, whose coefficients recursively all equal one.
This preserves the proposed paired-coefficient mathematics while eliminating
the need to introduce a separate series H and substitution by X squared.
The witness is a proof obligation, not a hypothesis.

## Falsifier

An index `n >= 1` with an even `a393867 n` would refute the target. A pair
with unequal residues would refute the proposed intermediate claim. The
finite probes found neither; the unbounded Lean theorems rule them out.

## Gap

Search receipts, in the required repository -> pinned mathlib -> external
ecosystem order:

- Repository D5: `rg` for `A39386[678]`, `a393867`, and `convolution_pairing`.
  Read all 278 lines of `PrimePowerShiftLogDerivative`, including private
  helpers. `generating_equation`, `lt_prime`, and the inverse definition are
  reusable. `hanna_conjecture` proves prime divisibility only, which does not
  imply oddness. `printed_formula_false` concerns the shifted formula only.
  `prime_dvd_coeff_pow` controls divisibility by the indexing prime, not two.
  Its private `coeff_mul_vanish` shows the useful lowest-coefficient pattern.
- Read the general public `convolution_pairing` in
  `ConvolutionRecurrenceOddPowersOfTwo`; that module is `generality: I`, so
  this G module cannot import it (SL-010). The derivative route does not need it.
- Pinned mathlib: Lean v4.33.0, mathlib
  `db584cd6d46c92f209a44c0f1c829460d327499d`. Exact OEIS identifiers absent;
  `Hanna` hits are unrelated names. Located `coeff_derivative`,
  `derivative_pow`, and `ZMod.intCast_eq_one_iff_odd` for direct reuse.
- OEIS JSON query `id:A393866|id:A393867`, fetched successfully (HTTP 200):
  both entries returned; A393867 still prints both conjecture comments.
- GitHub code API: exact queries `"A393867" language:Lean` and
  `"A393866" language:Lean` each returned total_count=0, incomplete_results=false.
- Loogle: `PowerSeries, "derivative"` returned 30 declarations, including the
  power rule. The logarithm results require rational-algebra hypotheses and
  do not prove the characteristic-two paired-coefficient statement.
- arXiv API: `all:A393866 OR all:A393867` returned totalResults=0;
  `(all:prime AND all:Hanna) AND (all:logarithmic OR all:"power series")`
  also returned totalResults=0. Both responses were valid Atom feeds with
  the exact query echoed. No failure is counted as a negative result.
  No proof found in this explicit search scope; no global absence claim.

## Evidence

### Numerical semantic echo

Independently ran the specified strict-prefix Miller recurrence at N=100,
asserting both exact Miller division and `prime n | c_n` at each step, then
used `g_n = n*F_n - sum_(k=1..n-1) g_k*F_(n-k)`.
All 100 prime-divisibility assertions passed. F's first 21 coefficients and
g's first 20 coefficients match the directly fetched OEIS DATA exactly.
No even g term among indices 1 through 100; no failure among the 50 pairs
`(F_(2m),F_(2m+1))`, m=0 through 49. F at indices 1 through 100 has 41 even
and 59 odd entries, agreeing with the brief. At indices 0 through 99 the
counts are 40 and 60; this is an indexing distinction, not a conflicting run.
F parity at indices 0 through 20:
`1,1,0,0,0,0,1,1,0,0,0,0,1,1,1,1,1,1,1,1,0`.
These checks are probes, not a finite positive formal instance or progress
toward the unbounded theorem.

### Build receipts

`make lean-cache-ensure`: EXIT=0; `LEAN_CACHE` status=seeded,
method=clonefile, donor=/Users/chronoai/trureturing, clonefile_attempts=1,
stamp_miss=null; project and mathlib olean states both warm.
The first genuine Lean attempt implemented the defect power rule and the
strong induction `defect_f_zero`. Initial errors were zero-coefficient
rewrites, the distinction between `constantCoeff` and `coeff 0`, and a
nonexistent `ZMod.eq_zero_or_eq_one` name. These were repaired using explicit
Mathlib coefficient rewrites and a private kernel `decide` on `ZMod 2`.
The file-level hot-cache compilation now exits 0 and proves `defect_f_zero`
without `sorry` or added axioms. This is an unbounded structural lemma, not
a finite-check progress claim; the target theorem is still pending.

Next checkpoint: both public theorems `generating_coeff_pair` and
`a393867_odd` compile (file-level EXIT=0), with `#print axioms` reporting only
`propext`, `Classical.choice`, and `Quot.sound` for each. The main theorem
uses `generating_coeff_pair` through `paired_derivative` and
`log_mod_two_identity`; the paired result is on the live derivation path.
Project build, report, emission, content checks, and freezing remain pending.

Formal project gate: `make lean` EXIT=0, wall time 403.526 seconds on this
macOS worktree. `LEAN_CACHE` status=present, method=none, stamp_miss=null,
project_olean_state=warm, mathlib_olean_state=warm, mathlib_missing_olean_files=0;
the earlier donor seed is recorded above. Lake reports successful completion
of 12,896 jobs. This is a local build reading, not a CI timing claim.
The directory now contains 27 files; the original frozen source has no diff.

Canonical report gate: `make lean-report` EXIT=0, wall time 558.407 seconds.
The producer completed after its full fallback inspected 78,025 declaration
material files. Output: `.lake/build/stratalint/raw-lean-report.json`, SHA-256
`6ea9e580cc684cc4f0698ba4bf2d8b18a360d1da59573a487695f541ad655f57`;
input address
`sha256:bb401f2f55ac34c9a3c75ff21cf9221fe176fcafe975902db20c7b323e2beef1`.
The adjacent `.provenance.json` records the canonical producer receipt.

First `make emit`: EXIT=2, 19.593 seconds. Scribe rejected the newly added
problem-resolution claim with `invalid-problem-resolution-source`, because
the target module was not frozen yet. The correction is sequencing: emit
the theorem descriptions, freeze canonically, then attach the resolution
claim and re-emit. The Lean proof is unchanged by this correction.
The corrected pre-freeze `make emit` exits 0 in 65.568 seconds and generates
the new Blueprint with both universal statements and their proof explanations.

Pre-freeze `scribe-content-checks.sh` with the canonical report and exact
base above: EXIT=0, 23.643 seconds. The changed paths select Describe and
Markdown checks; Describe reports `red=0`, and KaTeX reports
`judged=1 formula(s)=2 red=0`. The projection check is not selected by this
delta (no projection JSON or producer change). The offline DOI observations
concern repository library notes; they do not constitute online verification
or a failed check.

### Elaborated dependency query

A Lean `run_cmd` query used `Environment.find?`, `ConstantInfo.type`,
`value? (allowOpaque := true)`, and `Expr.getUsedConstants`, recursively
expanding this module's private helpers and stopping at the frozen D5
boundary. EXIT=0. It confirmed the four edges listed below, not just textual
name matches. The paired theorem's boundary contains `lt_prime`, `prime`,
`generatingSeries`, and `generating_equation`. The final theorem additionally
contains `logDerivative`, its generated defining equation, and `a393867`.
This confirms constant dependencies; live use is separately checked by
reading the short coefficient derivation, not inferred from the graph alone.

## ASSUMED-UNVERIFIED

No priority, exhaustive literature search, A393868 result, or completed
PR is claimed at this checkpoint. A393866 and A393868 b-files were not opened:
`ASSUMED-UNVERIFIED`. The user's arXiv search report is not represented as a
search performed by this worker. No theory volume or atom will be created.

## Triage

`theorem`: the exact target is proved by `a393867_odd`. Its Scribe node records
the resolution; project gates and PR publication are still pending here.

### Theorem admission analysis

Both public declarations have `proof_shape: content` and
`admission_basis: escape-witness`. `utility: none`: these are unbounded
symbolic statements proved by induction and formal-series algebra, not
bounded enumeration, a checker, numerical reduction, or a certified finite
instance. The private initial coefficient and the two-element coefficient
field calculation only support the universal proof.

For `generating_coeff_pair`, the new construction is the strong induction in
`defect_f_zero`, which derives the paired-coefficient conclusion itself
(the second legitimate witness form in CLAUDE 3.2). It uses a newly established
coefficient at every even degree; its proof cannot be reduced to instantiation
or projection of the frozen source equations. The independent intermediate
power-defect equality `defect_pow` supports that induction, but its algebraic
normalization alone is not claimed as the novel content.
The four checks for this first declaration are: (i) `defect_f_zero` occurs
in its elaborated dependency closure; (ii) its strong induction establishes
new coefficients, beyond frozen instantiation/projection/normalization;
(iii) this invokes the explicitly permitted conclusion-as-construction
form, rather than presenting an equivalent rewrite as an independent
intermediate witness; (iv) the even-coefficient extraction consumes the
induction result directly and no projected-away or dead component is involved.

For `a393867_odd`, the named witness is `generating_coeff_pair`:

1. Dependency closure: the chain is `a393867_odd` -> `log_mod_two_identity`
   -> `paired_derivative` -> `generating_coeff_pair` -> `defect_f_zero`.
2. Not a frozen projection: the frozen source only defines the series and
   proves divisibility by the nth prime. The new strong induction is needed
   to prove the coefficient pairing modulo two.
3. Not definitionally equivalent: pairing concerns coefficients of F;
   the target concerns coefficients of its derivative times its unit inverse.
   Formal differentiation, inversion, and a second induction connect them.
4. Live path: `paired_derivative` uses the equality for each even degree;
   `log_mod_two_identity` multiplies that equality by the inverse, and the
   final coefficient induction uses this product identity. No discarded
   conjunction or unused witness is used to establish the dependency.

There are no unrelated public companions. The directed consumer edge is
`a393867_odd` -> `generating_coeff_pair` and answers exactly the preregistered
oddness conjecture. The only direct frozen module is
`D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative`, state pin
`sha256:ac377909f3efe06da244e7960fe628f1ea740f752641f94947b75c57a790b785`.
The source theorem dependencies are `generating_equation` and `lt_prime`;
the original definitions `generatingSeries`, `prime`, `logDerivative`, and
`a393867` retain their meanings. Declaration-level identities were read from
the canonical Lean report and matched exactly by `name_key` against accepted
frozen event `1cf1333b827273fcb1f83e0f21fa6ea633bbdf882aefa1b6c956dc68f5ae02ee`.
No statement hashes were recomputed by the worker. Each short name below
denotes the full GID
`D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.<name>`.

| Direct frozen declaration | statement_id | Consumers |
| --- | --- | --- |
| `lt_prime` | `sha256:6d1e9781ad95c0927e40e35b903401eb5faf74d76a655668f525adba8d384c59` | pair, oddness |
| `prime` | `sha256:0a736efbf5ea49c36d6d348f1d3d21b17714ff433baaef1d2acb118a193af86b` | pair, oddness |
| `generatingSeries` | `sha256:ad6449b1161b2a32010488990c77aa6cc3957460926b53e14e221181bdf878f2` | pair, oddness |
| `generating_equation` | `sha256:b84125e62ee76082f046bc175964b51643eb15f3e07d6724e55078008a79ea29` | pair, oddness |
| `logDerivative` | `sha256:43ab45a43a98fbbf4e86ca7e249c35dbbf819eb18188389589c7c3e964d0afb7` | oddness |
| `a393867` | `sha256:e653feadb8c579450bd4c1a9151aaf899c9ba14e6be38a8e6c19b7000b7d1968` | oddness |

The elaborator-generated `logDerivative.eq_1` is accounted for under its
owning definition `logDerivative`; it is not a separate frozen public
statement. The pair and oddness declarations' own report identities are,
respectively, `sha256:01499cf51fce67e5b2ceb7d214f3d5a5fbe97157562324039dee651f6a58346d`
and `sha256:3324701a7dfdca32def1679d93600fd9ad5950d7dfd0a4390ea04493efed0583`.
