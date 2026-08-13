# PZG theorem 6.48 golden-fiber atom: open report

## Disposition

`open`.

The selected atom is not closed by the repository's existing golden-fiber
declarations.  One frozen declaration proves the later theorem 6.48-prime's
Beatty coordinate formulas, and another proves an equality between the two
first-index formulas mentioned in corollary 6.48-double-prime.  The selected
theorem 6.48 additionally requires the fiber predicate, an exactly specified
real interval of length `2 * phi^3`, a parity condition, the two possible
fiber capacities, monotonicity of the second coordinate, interval support, a
first-member theorem, and certificate evidence.  Those clauses have no single
faithful Lean counterpart.

There is also a statement-echo blocker: the authoritative text states that the
fiber is "a real interval of length `2 phi^3` plus parity", but it does not give
the interval's endpoints or boundary convention.  Choosing those data would
invent a stronger, weaker, or merely different claim.  The ambiguity cannot be
resolved from theorem 6.48-prime or corollary 6.48-double-prime, which explicitly
retain this interval formulation only at the conceptual level.

No Lean, Blueprint, Scribe, receipt, frozen-ledger, or digestion file was
modified.  In particular, the coordinate formula or the existing first-index
equality is not being deposited as a weakened replacement for the whole atom.

## Environment and atom selection

The work was performed in the dispatcher-assigned isolated lane:

```text
pwd -P = /Users/mstudio3/trureturing-diag-lane-a-20260814
git rev-parse --show-toplevel = /Users/mstudio3/trureturing-diag-lane-a-20260814
branch = harness/diag-lane-a-20260814
baseline HEAD after latest origin/dev merge = 12dbe1b00884b183a31522dcd63a71b4e043082a
origin/dev = 600528ed47fd08001838b5db51de4bb71f12936e
git merge-base --is-ancestor origin/dev HEAD: rc 0
```

`make dotnet` exited `0`.  The formalization skill requests a PATH export from
`Meta/StrataLint/scripts/local-harness-gate.sh`, but that file is absent in this
checkout (`test -e ...` exited `1`), so no PATH mutation was made.

The live deposit-shape query was:

```sh
git log --no-merges -20 --format='%H %s' --grep='^formalize: deposit'
```

Its newest hit was:

```text
9da126e6d795a4b01d442020b41b9724a6a2b578 formalize: deposit D5/S1/FixedPoints/ThreeCycleGap.three_cycle_has_fixed_point_gap
```

The selected authoritative atom is `docs/develop/theory/PZG_BEDC.md`,
`theorem/6.48`.  It was obtained with:

```sh
make show-atom \
  ATOM_ID=pzg-residual-59dcfff740646b50b1ee831a17703e072eba56fe83a2b4b37f6d1ae22141b9de
```

The command exited `0` and reported:

```text
SHOW_ATOM atom_id=pzg-residual-59dcfff740646b50b1ee831a17703e072eba56fe83a2b4b37f6d1ae22141b9de source_id=pzg-v170 source_path=docs/develop/theory/PZG_BEDC.md atomizer=pzg-v1 ast_path=theorem/6.48
HASH_VERIFY raw_sha256=sha256:59dcfff740646b50b1ee831a17703e072eba56fe83a2b4b37f6d1ae22141b9de normalized_sha256=sha256:59dcfff740646b50b1ee831a17703e072eba56fe83a2b4b37f6d1ae22141b9de cas_ref=sha256:59dcfff740646b50b1ee831a17703e072eba56fe83a2b4b37f6d1ae22141b9de status=match
```

The complete `BEGIN_RAW_TEXT` returned by that command is:

```text
**定理 6.48(纤维坐标:6.42 之闭合)**〔closed;复核修正一处〕。a(v) = 2S(v) − 3v,b(v) = 2v − S(v)(全词证书);纤维判据 v ∈ 纤维 a ⟺ 2S(v) = 3v + a——一条长 2φ³ 之实区间加奇偶 v ≡ a (mod 2),容量 {⌊φ³⌋, ⌈φ³⌉} 证毕;b = (v − a)/2 沿纤维单调 ⇒ 支撑必整区间;起点闭式经复核修正为 **m(a) = ⌊aφ − φ²⌋ + 1**(原提案 ⌈aφ − φ²⌉ 于 a = 1 失效:aφ − φ² 恰为整数,ceil 不进位;修正式 a ≤ 6 全对)。6.42 之前沿余项整体闭合。
```

The atom-specific formalization receipt search was:

```sh
rg -n -F \
  'pzg-residual-59dcfff740646b50b1ee831a17703e072eba56fe83a2b4b37f6d1ae22141b9de' \
  Meta/Digestion/formalizations
```

It exited `1` with no output.  The atom remains a residual-open ledger entry
with empty coverage and Scribe receipts.

## Clause-level echo

| Authoritative source clause | Required formal counterpart | Evidence/status |
|---|---|---|
| `a(v) = 2S(v) - 3v`, `b(v) = 2v - S(v)` | Natural-number domain for `v`, the chapter's displacement decoding `S`, and two integer coordinate definitions/theorems | **Partial.** `GoldenFiberCoordinates` defines `fiberA` and `fiberB` from its local floor-based `goldenShift`; `ZeckendorfDisplacementReading.displacement_decode_eq_beatty_floor` proves the chapter's displacement decode equals that floor expression.  No public theorem assembles that bridge with every 6.48 clause. |
| `(全词证书)` | A specified, reproducible certificate over the claimed word domain, or a proof replacing that finite certificate | **Missing/ambiguous.** The atom does not specify the enumerated word domain or certificate artifact, and no matching receipt was found. |
| `v` is in fiber `a` iff `2S(v) = 3v + a` | An explicit fiber set/predicate and an iff theorem against the coordinate equation | **Missing.** Defining the fiber to be this equality would make the criterion tautological and would not connect it to the source's Witt-word fiber. |
| “a real interval of length `2 phi^3` plus parity `v == a (mod 2)`” | Exact real endpoints, open/closed boundary convention, coercions, the interval-length equality, and the congruence conjunction | **Blocked by source ambiguity and missing declaration.** Length alone does not determine an interval; the atom supplies neither endpoints nor boundary convention. |
| Capacity is in `{floor(phi^3), ceil(phi^3)}` | Finiteness of every `a`-fiber and an exact cardinality disjunction/equality | **Missing.** No matching `Set`/`Finset` fiber-cardinality theorem exists. |
| `b = (v-a)/2` is monotone along a fiber | Integrality from parity, equality with the second coordinate, and an order theorem for two members of the same fiber | **Missing.** The displayed algebra is not stated as a repository theorem, and no fiber order structure is present. |
| Therefore the `b`-support is an integer interval | A precise support set and interval/no-gap theorem, including endpoints | **Missing.** No such support declaration was found. |
| Corrected start `m(a) = floor(a*phi - phi^2) + 1` | A theorem that this value is the least member/index of fiber `a`, with the source's domain for `a` | **Partial only.** `GoldenFiberFirstIndex.golden_fiber_first_index_forms_eq` proves equality with `floor((a-1)*phi)` for positive `a`; it neither defines `m` nor proves membership or leastness. |
| The old ceiling proposal fails at `a = 1` because the argument is integral | A checked counterexample to the old formula and the exact integrality calculation | **Missing.** The current first-index module does not state this counterexample. |
| “the corrected formula is right for `a <= 6`” | A bounded universal theorem or replayable finite certificate with explicit lower bound | **Missing/underspecified.** No matching certificate was found, and the lower endpoint/domain is not written in this clause. |
| “the residual before 6.42 is wholly closed” | Coverage of the complete proposition 6.42 frontier: both capacity pairs, interval supports, and Sturmian distribution/certificate claims | **Not established.** Proposition 6.42 remains its own open atom, `pzg-residual-4fbb4559ff083825538058554dbc97b2e34531edb09042901af0ec7ac107a8e4`, with no formalization receipt. |

The dropped-or-weakened set is therefore nonempty.  In particular, proving
only the coordinate identities or equality of two candidate first-index
formulas does not prove the fiber interval, cardinality, support, leastness, or
certificate claims.

## Existing partial declarations and receipts

`D5/S1/Words/GoldenFiberCoordinates.lean` defines `goldenShift`, `fiberA`, and
`fiberB`, then proves:

```text
D5/S1/Words/GoldenFiberCoordinates.golden_fiber_coordinates
```

That declaration is a faithful closure of the separate theorem 6.48-prime,
whose authoritative atom is
`pzg-residual-3d814b4870e48295d7a46b0f6b6375a28a0c8408b554c4605d619dea9b8711f7`.
Its receipt maps exactly to `golden_fiber_coordinates`.  The theorem states the
two Beatty floor formulas and their sum; it does not mention a fiber set,
interval, parity, cardinality, monotonicity, support, or first member.

`D5/S1/Deficit/GoldenFiberFirstIndex.lean` proves:

```text
D5/S1/Deficit/GoldenFiberFirstIndex.golden_fiber_first_index_forms_eq
```

Its receipt belongs to the separate corollary 6.48-double-prime atom
`pzg-residual-cf9baaa31ab25595123db0ce7a726abe57bd6a78608026f9da57dd5ce7b0468c`.
The emitted Blueprint calls it an “honest partial closure” and explicitly says
the Beatty fiber criterion, image, capacity, and joint coordinate-family claims
remain unresolved.  Equality of two floor expressions is not a theorem that
either expression is the first member of a fiber.

Both partial modules have active Freeze events:

```text
Golden/Frozen/accepted/bfe1f38303dd416c70cde78691520f855bedfe61af7634588a41f321d7df6f9f.json  (GoldenFiberCoordinates)
Golden/Frozen/accepted/9d469d77a0dd43f2dfd35e07d8e20fcfa7218ca5da7c0d7dab9b6e6b7d9d11d2.json  (GoldenFiberFirstIndex)
```

The exact check was:

```sh
for p in D5/S1/Words/GoldenFiberCoordinates.lean \
         D5/S1/Deficit/GoldenFiberFirstIndex.lean; do
  printf '%s: ' "$p"
  grep -l -F "$p" Golden/Frozen/accepted/*.json
done
```

The Freeze events prohibit adding declarations to those files.  They are not,
by themselves, the reason for this `open` disposition: a faithful complete
theorem could live in a new module.  The stopping reasons are the unresolved
statement echo, absent source-fiber bridge, and missing certificate and proof
clauses above.

## Library search and failed approaches

The following repository searches were run verbatim:

```sh
rg -n "fiberA|fiberB|golden_fiber_coordinates|golden_fiber_first_index_forms_eq" \
  D5 Blueprint Meta/Digestion/formalizations

rg -n "Set.*fiber|Finset.*fiber|support.*fiber|fiber.*support|Monotone.*fiber|fiber.*Monotone|capacity|floor.*goldenRatio" \
  D5/S1

rg -n "goldenShift.*displacementDecode|displacementDecode.*goldenShift|displacementDecode_eq_floor|floor.*displacementDecode" \
  D5/S1

rg -n "GoldenFiber|golden_fiber|纤维坐标|纤维容量|4,4,4,5|全词证书" \
  Evidence Meta/Digestion/formalizations
```

The first search found only the two partial declarations, their mirrors, and
their two separate receipts.  The second found no theorem implementing the
selected fiber interval/parity/capacity/support bundle.  The third found the
displacement-to-floor theorem and a private local bridge used by a different
deficit theorem, not a complete fiber theorem.  The certificate search found
the two partial formalization receipts but no matching evidence artifact or
certificate for theorem 6.48.

Pinned Mathlib was searched with:

```sh
rg -n "Beatty|beatty" \
  .lake/packages/mathlib/Mathlib/NumberTheory \
  .lake/packages/mathlib/Mathlib/Algebra/Order/Floor

rg -n "goldenRatio.*floor|floor.*goldenRatio|goldenRatio.*ceil|ceil.*goldenRatio|goldenRatio \\^ 3" \
  .lake/packages/mathlib/Mathlib
```

The relevant upstream hit is `Mathlib/NumberTheory/Rayleigh.lean`, which
defines Beatty sequences and proves their complementary partition theorem.
It does not state this golden coordinate difference's fiber sizes, parity
interval, or first-index result.  Generic floor and golden-ratio identities are
prerequisites rather than a duplicate of the complete source claim.

The considered closure routes fail fidelity as follows:

1. Reusing `golden_fiber_coordinates` drops every structural and certificate
   clause after the coordinate formulas.
2. Reusing `golden_fiber_first_index_forms_eq` proves only that two formulas
   agree, not that their common value belongs to or starts the fiber.
3. Defining “fiber `a`” as `2*S(v) = 3*v+a` makes the requested iff true by
   definition while omitting the bridge to legal words; that is hollow relative
   to the source.
4. Guessing endpoints or open/closed boundaries from the stated interval
   length changes the claim without authoritative support.
5. Depositing any one of these partial substitutes under the selected atom
   would leave independently testable clauses unaccounted for and violate the
   statement echo.

## Fidelity and non-hollowness gate

This is an `open` report, so the deposit gate is intentionally not claimed
green:

- Conclusion substance: the source conclusions are nontrivial, but no faithful
  combined Lean declaration was produced.
- Hypothesis satisfiability: no exact hypothesis list can be checked until the
  fiber's interval endpoints, boundary convention, and certificate domain are
  specified.
- Domain inhabitance: natural numbers and integers are inhabited, but the
  source's legal-word fiber object has no selected formal declaration.
- Proof substance: no new proof was written.  A definition-only fiber criterion
  was rejected as hollow.
- Duplicate search: completed above; only strict partial results and generic
  Beatty machinery were found.
- Clause fidelity: failed for the interval specification, source-fiber bridge,
  capacity, monotonicity, support, leastness, and certificates.  This blocks
  deposit.
- Rendered-statement fidelity: not run because no Lean/Scribe declaration was
  created.

A future closure needs an authoritative exact interval predicate (including
endpoints and boundary convention), a formal legal-word/Witt fiber tied to the
displacement decoding, and a declared replacement or reproducible scope for
the “all-word” and `a <= 6` certificates.  It can then prove the cardinality,
order, interval-support, and least-member clauses in a new module importing the
existing frozen prerequisites.

## Unreached workflow steps

Because statement echo and clause fidelity fail, the following commands were
not run:

```text
make deposit ATOM_ID=pzg-residual-59dcfff740646b50b1ee831a17703e072eba56fe83a2b4b37f6d1ae22141b9de GID=<gid>
make preflight
make cover ATOM_ID=pzg-residual-59dcfff740646b50b1ee831a17703e072eba56fe83a2b4b37f6d1ae22141b9de GID=<gid>
make pr-open ...
```

No declaration GID exists for the complete atom.  `git diff --check` and
`make selftest` are run on this report before commit.  Deposit, preflight,
cover, and PR opening would be inappropriate after an evidence-complete
`open` disposition.
