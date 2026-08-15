# Diagonal Month R2 Lane C: GICT Theorem 1.5 Open Report

Outcome: `open`, with no formalization deposit and no partial cover.

This report records the assigned lane `harness/diag-month-r2-c` at
`/Users/mstudio3/trureturing-diag-month-r2-c`. Candidate reselection stopped
before this report. The selected atom is a coupled, multi-clause theorem whose
Zeckendorf and general three-gap legs have exact reusable declarations, and a
separate tower carrier proves boundary-completed Fibonacci gap counts. The DSI
collapse, tower-to-phase carrier bridge, and `N = 13` certificate obligations
still do not have a faithful common discharge in the current repository.

No Lean, Blueprint, Scribe, formalization receipt, frozen-ledger, or digestion
file was edited. In particular, no path under `Meta/Digestion/**`,
`Golden/Frozen/**`, or `Meta/Digestion/formalizations/**` was changed.

## Environment and baseline

The inherited lane was initially clean at
`e17a20fed21529321667d7c6dbf5ce915246f8a0`, four commits behind the live
`origin/dev`. Before renewing any atom evidence, the clean lane ran:

```text
git merge --no-edit origin/dev
exit = 0
result = fast-forward to e3d4b21439a18c1f143385a6f6f55a091cc4c06e

pwd -P
exit = 0
output = /Users/mstudio3/trureturing-diag-month-r2-c

git rev-parse --show-toplevel
exit = 0
output = /Users/mstudio3/trureturing-diag-month-r2-c

git rev-parse HEAD
exit = 0
output = e3d4b21439a18c1f143385a6f6f55a091cc4c06e

git rev-parse origin/dev
exit = 0
output = e3d4b21439a18c1f143385a6f6f55a091cc4c06e

git merge-base --is-ancestor origin/dev HEAD
exit = 0
```

The current PATH declaration was read from
`tools/scripts/local-harness-gate.sh`, including `/usr/sbin`, and applied for
the canonical build commands. `git status --short` was empty before this
report was added.

## Atom and authoritative statement

- Atom ID:
  `gict-residual-6706f5aca56b416822592bfdf174870340ad95de2896373968b828ba4a49f0c4`
- Source ID: `gict-v3.6`
- Source: `docs/develop/theory/GICT.md`, `theorem/1.5`
- Atomizer: `gict-v1`
- Claim class: coupled multi-clause theorem plus concrete certificate, with
  partial frozen coverage and missing bridges/data; it is not a single-clause
  certificate or a legal partial-cover target.

The authoritative command was:

```sh
make show-atom \
  ATOM_ID=gict-residual-6706f5aca56b416822592bfdf174870340ad95de2896373968b828ba4a49f0c4
```

It exited `0` and reported:

```text
SHOW_ATOM atom_id=gict-residual-6706f5aca56b416822592bfdf174870340ad95de2896373968b828ba4a49f0c4 source_id=gict-v3.6 source_path=docs/develop/theory/GICT.md atomizer=gict-v1 ast_path=theorem/1.5
HASH_VERIFY raw_sha256=sha256:6706f5aca56b416822592bfdf174870340ad95de2896373968b828ba4a49f0c4 normalized_sha256=sha256:6706f5aca56b416822592bfdf174870340ad95de2896373968b828ba4a49f0c4 cas_ref=sha256:6706f5aca56b416822592bfdf174870340ad95de2896373968b828ba4a49f0c4 status=match
```

Raw, normalized, and CAS SHA-256 values all match `6706f5...`. The complete
authoritative raw text was:

```text
**定理 1.5(三重离散)**〔定理·典 ×3〕。
(乘)DSI:log_φ 尺上 φⁿ 落整数格——连续标度群塌缩为 ⟨×φ⟩;
(加)Zeckendorf:每 n∈ℕ 唯一写成非相邻 W-位和;进位 11→100 有限归约 ⟹ **Z(m+n)=𝒩(Z(m)+Z(n))**;
(几)三距定理:{nφ} 之 N 点间距 ≤3 种,N=Fibonacci 时恰 2 种。
〔证书:几何重反例扫描——N=13 时 φ 独占 2 种,银比/e/π/√2 皆 3 种;轮 162〕
```

## Clause-level echo

No source clause is dropped from this accounting.

1. **DSI integer log-scale.**
   `D5.S1.Scale.logScale_phiUnit_zpow_mul` proves that multiplying a nonzero
   golden integer by the unit `phi^n` translates its integral logarithmic
   scale by exactly `n`. Its private supporting lemma proves
   `log_phi(phi^n) = n`.
2. **DSI group collapse.**
   `D5.S1.Scale.golden_units_eq_signed_phi_pow` proves that every golden
   integer unit is a signed integral power of `phi`, and
   `goldenUnitsMulEquiv` identifies the unit group with the integral exponent
   part times sign torsion. These are substantive precursors, but the atom says
   a *continuous scaling group* collapses to `⟨×phi⟩`. No source or repository
   declaration defines that continuous group, a collapse/selection map, or an
   exact theorem relating it to the golden-integer unit group. Binding the
   entire DSI clause to the unit classification would silently choose a domain
   and replace a collapse outcome with an intrinsic unit-group description.
3. **Unique nonadjacent W representation.**
   `D5.S0.Conventions.wdigits_isCanonical`, `decode_wdigits`, and
   `wdigits_unique` map respectively to nonadjacency/canonicality, decoding to
   `n`, and uniqueness. `wEncoding : Nat ≃ WDigitString` packages the complete
   canonical equivalence.
4. **Finite carry normalization and addition.**
   `D5.S1.Digit.Normalize.normalize` is defined by a decreasing lexicographic
   measure; `normalize_reachable`, `normalize_canonical`, and
   `rawValue_normalize` establish finite local carry reduction, canonicality,
   and value preservation. `D5.S1.Digit.zeck_add` is the exact addressable
   equality
   `toRaw (Z (m+n)) = normalize (toRaw (Z m) + toRaw (Z n))`.
5. **At most three golden-orbit gaps for every N.**
   `D5.S1.Phase.goldenOrbit` is the source orbit, `goldenGapValues` is its
   cyclic adjacent-gap set, and `D5.S1.Phase.three_gap` proves
   `(goldenGapValues N).card <= 3` for every natural `N`. This is exact coverage
   for the general at-most-three clause.
6. **Exactly two gaps at Fibonacci time.**
   The tower library has substantially more than the internal-neighbour result
   `GoldenGaps.adjacent_gap_spectrum`. Public
   `D5.S0.Tower.GoldenGapFrequency.fullGap Q` indexes
   `Nat.fib (Q + 2)` sorted golden-name gaps and includes the terminal gap to
   one. Public `golden_full_gap_counts` proves that, for `2 <= Q`, its large and
   small counts are `Nat.fib (Q + 1)` and `Nat.fib Q`, with their sum equal to
   the level cardinality. Its proof-local private `fullGap_spectrum` establishes
   pointwise that every such boundary-completed gap has one of the two golden
   lengths. Public `GoldenGapWord.golden_full_gap_word` and
   `golden_gap_word_step`, together with
   `GoldenGapZeckendorf.goldenGapWord_eq_zeckendorf_word`, expose the resulting
   Fibonacci word and its Zeckendorf classification. Thus exact-two Fibonacci
   machinery is present on the tower `fullGap` carrier; the private spectrum
   lemma is proof support, while the public counts and word theorems are the
   addressable outcomes.

   What is missing is an addressable carrier-identification theorem equating
   this boundary-completed tower family with
   `ThreeGap.gaps Real.goldenRatio (Nat.fib (Q + 2))` (or equivalently proving
   the corresponding statement for `D5.S1.Phase.goldenGapValues`). The focused,
   name-bounded current-tree and all-ref searches below found no declaration
   mentioning both carriers. This is evidence for the addressability gap, not a
   claim that text search proves global mathematical nonexistence; the tower
   theorem cannot silently be rebound as the source's phase-orbit theorem.
   `ThreeGap.three_gap_lengths_eq` is conditional on already having exactly
   three gaps and only identifies those three lengths; it cannot prove the
   exact-two Fibonacci specialization.
7. **The `N = 13` comparative certificate.**
   A faithful counterpart needs a common gap-count function and checked values
   showing two gaps for `phi` and three for the silver ratio, `e`, `pi`, and
   `sqrt 2`. No Lean declaration, Evidence record, Golden datum, or
   content-addressed observation receipt containing that comparison was found.

The missing set is the DSI collapse carrier/map, the tower-`fullGap`-to-phase-
`ThreeGap.gaps` Fibonacci bridge, and all five checked `N = 13` comparative
values. The exact-two tower machinery itself is not missing.

## Exact-reference, receipt, and history audit

The following commands were run verbatim in the synchronized lane:

```sh
rg -n -F \
  'gict-residual-6706f5aca56b416822592bfdf174870340ad95de2896373968b828ba4a49f0c4' \
  .
```

Exit `1`, no current-tree hit.

```sh
rg -n -F \
  'gict-residual-6706f5aca56b416822592bfdf174870340ad95de2896373968b828ba4a49f0c4' \
  Meta/Digestion/formalizations docs/reports
```

Exit `1`, no formalization receipt or prior tracked report.

```sh
git log --all --oneline \
  -S'gict-residual-6706f5aca56b416822592bfdf174870340ad95de2896373968b828ba4a49f0c4'
```

Exit `0`. Its only hits were the ingestion/migration commits
`80a9836e`, `0f0edb92`, and `5f34ebbd`; no theorem deposit, cover, or report
commit was found.

## D5 and pinned-mathlib searches

```sh
rg -n 'wdigits_isCanonical|decode_wdigits|wdigits_unique|wEncoding|zeck_add' \
  D5 --glob '*.lean'
```

Exit `0`; the exact defining hits are in `WDigits.lean` and `Addition.lean`.

```sh
rg -n --glob '*.lean' \
  'fullGap|largeGapCount|smallGapCount|golden_full_gap_counts|fullGap_spectrum|golden_full_gap_word|golden_gap_word_step|goldenGapWord_eq_zeckendorf_word' \
  D5/S0/Tower/GoldenGapFrequency.lean D5/S0/Tower/GoldenGapWord.lean \
  D5/S0/Tower/GoldenGapZeckendorf.lean
```

Exit `0`; it found public `fullGap`, both public count definitions,
`golden_full_gap_counts`, the public gap-word/Zeckendorf theorems, and the
private `fullGap_spectrum` proof support described above.

```sh
rg -n --glob '*.lean' \
  'fullGap|golden_full_gap_counts|golden_full_gap_word|goldenGapWord_eq_zeckendorf_word' \
  D5/S1/Phase
```

Exit `1`; the Phase modules contain no bridge from the tower carrier. The
converse focused search found only the Phase definitions in
`ThreeDistance.lean` and no `ThreeGap.gaps`, `goldenGapValues`, or `goldenOrbit`
reference in the three tower modules.

```sh
rg -n --regexp \
  'continuous.*(scale|scaling)|scale.*(continuous|collapse)|scaling.*(group|collapse)|cyclic.*scal|⟨×φ⟩|phiUnitZPowMul|logScale_phiUnit_zpow_mul|golden_units_eq_signed_phi_pow|goldenUnitsMulEquiv' \
  D5 --glob '*.lean'
```

Exit `0`; the relevant unique hits are the log-scale translation and
golden-unit classification/equivalence described above. There is no hit
defining a continuous scaling group or a collapse map.

```sh
rg -n \
  'goldenGapValues.*Nat\.fib|Nat\.fib.*goldenGapValues|goldenOrbit.*Nat\.fib|Nat\.fib.*goldenOrbit|fullGap.*(ThreeGap|goldenGapValues|goldenOrbit)|(ThreeGap|goldenGapValues|goldenOrbit).*fullGap' \
  D5 --glob '*.lean'
```

Exit `1`; this focused, name-bounded search found no Fibonacci-time
tower-to-phase carrier bridge. It is not presented as a globally complete
semantic proof of absence.

```sh
rg -n --regexp \
  'ThreeGap\.(gaps|orbit).*(13|Nat\.fib)|(13|Nat\.fib).*ThreeGap\.(gaps|orbit)|goldenGapValues 13|goldenOrbit 13|silverRatio|silver ratio' \
  D5 Evidence Golden --glob '*.lean' --glob '*.json' --glob '*.toml'
```

Exit `1`; no exact Fibonacci/13/silver-ratio theorem or certificate datum.

```sh
rg -n --regexp \
  'theorem three_gap|theorem adjacent_gap_spectrum|theorem zeck_add|theorem wdigits_unique|theorem logScale_phiUnit_zpow_mul|theorem golden_units_eq_signed_phi_pow|def goldenUnitsMulEquiv' \
  .lake/packages/mathlib/Mathlib D5 --glob '*.lean'
```

Exit `0`. All displayed repository wrappers/classifications are D5
declarations. The pinned mathlib source supplies Zeckendorf machinery used by
`WDigits`; no second exact theorem for the complete four-obligation atom was
found.

## All-ref searches

`git for-each-ref --format='%(refname)' | wc -l` exited `0` and reported
`1475` refs. The following bounded all-ref searches were run verbatim. Each
uses `sort -u` so repeated copies of the same file line across refs do not
masquerade as distinct theorem shapes.

```sh
set -o pipefail
git grep -n -h -E \
  'DSI|discrete[- ]scale|discrete scaling|continuous scale|scale group|logb Real\.goldenRatio' \
  $(git for-each-ref --format='%(refname)') -- 'D5/**/*.lean' | sort -u
```

Exit `0`; the only relevant unique shapes are `logScale`, the private
`log_phi(phi^n)=n` lemma, and their scale-coordinate consumers. No addressable
continuous-group collapse theorem appeared.

```sh
set -o pipefail
git grep -n -h -E \
  'wdigits_isCanonical|decode_wdigits|wdigits_unique|wEncoding|zeck_add' \
  $(git for-each-ref --format='%(refname)') -- 'D5/**/*.lean' | sort -u
```

Exit `0`; this reproduced the current-tree Zeckendorf declarations and their
consumers, with no distinct complete-atom theorem.

```sh
set -o pipefail
git grep -n -h -E \
  'goldenOrbit|goldenGapValues|three_gap|adjacentGapSpectrum|adjacent_gap_spectrum|fullGap|golden_full_gap_counts|golden_full_gap_word|goldenGapWord_eq_zeckendorf_word' \
  $(git for-each-ref --format='%(refname)') -- 'D5/**/*.lean' | sort -u
```

Exit `0`; it found the current imported three-gap implementation, historical
axiom-debt forms, the golden-name spectrum theorem, and the boundary-completed
`fullGap` frequency/word/Zeckendorf family. The latter includes the public
Fibonacci multiplicity theorem and private pointwise spectrum proof; it found
no theorem identifying that family with the Fibonacci-time phase orbit.

```sh
set -o pipefail
git grep -n -h -E \
  'goldenGapValues.*Nat\.fib|Nat\.fib.*goldenGapValues|goldenOrbit.*Nat\.fib|Nat\.fib.*goldenOrbit|fullGap.*(ThreeGap|goldenGapValues|goldenOrbit)|(ThreeGap|goldenGapValues|goldenOrbit).*fullGap' \
  $(git for-each-ref --format='%(refname)') -- 'D5/**/*.lean' | sort -u
```

Exit `1`; no all-ref bridge hit.

```sh
set -o pipefail
git grep -n -h -E \
  'ThreeGap\.(gaps|orbit).*(13|Nat\.fib)|(13|Nat\.fib).*ThreeGap\.(gaps|orbit)|goldenGapValues 13|goldenOrbit 13|silverRatio|silver ratio' \
  $(git for-each-ref --format='%(refname)') -- \
  'D5/**/*.lean' 'Evidence/**/*.json' 'Evidence/**/*.toml' 'Golden/**/*.toml' | sort -u
```

Exit `1`; no all-ref exact certificate or missing bridge appeared.

## Frozen declarations and compilation

The reusable modules all have active Freeze events. Representative current
records are:

- `WDigits.lean`: `2036db62...json` (plus later reattestations)
- `Addition.lean`: `66a6dfba...json` (plus later reattestations)
- `Scale/Log.lean`: `65076f23...json` (plus later reattestations)
- `Scale/Units.lean`: `5eba0358...json`
- `Scale/UnitGroup.lean`: `819f58d1...json`
- `ThreeDistance.lean`: `154937ed...json` (plus reattestation)
- `GoldenGaps.lean`: `4cac3a56...json`
- `GoldenGapFrequency.lean`: `0de6837d...json`
- `GoldenGapWord.lean`: `f95df081...json`
- `GoldenGapZeckendorf.lean`: `ad70a1df...json`

The scoped verification command was:

```sh
lake build D5.S0.Conventions.WDigits D5.S1.Digit.Addition \
  D5.S1.Scale.Log D5.S1.Scale.Units D5.S1.Scale.UnitGroup \
  D5.S1.Phase.ThreeDistance D5.S0.Tower.GoldenGaps \
  D5.S0.Tower.GoldenGapFrequency D5.S0.Tower.GoldenGapWord \
  D5.S0.Tower.GoldenGapZeckendorf
```

It exited `0` with `Build completed successfully (8581 jobs)`. Lean replayed
an existing long-line linter warning in `UnitGroup.lean`; this report did not
edit that frozen file. `make dotnet` also exited `0`, building all Release
projects with zero warnings and zero errors.

## Failed approaches and partial-coverage refusal

- **Bind the full atom to the union of existing declarations:** rejected.
  A list of theorems is not coverage when three source obligations remain
  unrepresented.
- **Use the unit-group classification as DSI collapse:** rejected as a
  domain/outcome substitution. It proves an intrinsic classification of
  golden integer units, not collapse of a defined continuous scale group.
- **Use `three_gap` for the full geometric clause:** rejected because `<= 3`
  for every `N` does not entail `= 2` at Fibonacci `N`.
- **Use the tower `fullGap` theorems directly for Fibonacci time:** rejected as
  a carrier substitution. They do prove boundary-completed exact-two lengths,
  exact Fibonacci multiplicities, and the induced word, but no theorem equates
  `fullGap Q` with `ThreeGap.gaps Real.goldenRatio (Nat.fib (Q + 2))` or
  `goldenGapValues`.
- **Derive exact two from `three_gap_lengths_eq`:** rejected. That theorem
  assumes the card is already three and characterizes the three-value case.
- **Recompute or invent the `N = 13` scan:** rejected by the fabrication ban.
  The atom attests a machine-checked scan but provides no replayable values,
  method, or receipt, and the repository contains none.
- **Deposit only Zeckendorf or `three_gap`:** rejected as a partial cover and
  duplicate. Those clauses are already named and frozen. Covering the coupled
  atom with either GID would falsely close the missing DSI, exact-two, and
  certificate clauses.
- **Add wrappers to frozen modules:** rejected both as duplicate wrappers and
  because active Freeze events prohibit adding declarations.

There was no failed Lean proof attempt: the workflow stopped at clause fidelity
and library completeness, before creating a theorem with omitted obligations.

## Fidelity and non-hollowness accounting

- **Conclusion substance:** the source conclusions are nontrivial, but no new
  conclusion was proposed. No `True`, definitional tautology, or hypothesis
  restatement was deposited.
- **Hypothesis satisfiability:** not applicable to a candidate signature
  because no signature was introduced. Existing reusable theorems compile;
  the missing clauses are unconditional source outcomes, not hypotheses that
  may legally be assumed.
- **Domain inhabitance:** existing domains (`Nat`, golden integers, phase
  orbits) are inhabited in their frozen modules. The source's continuous
  scaling-group domain is absent, so inventing an inhabitant would invent its
  semantics.
- **Proof substance:** exact reusable proofs are substantive. They were not
  repackaged as proof of the stronger conjunction.
- **Deposit substance:** no new definition or named theorem was created; a
  wrapper around frozen results would not earn a freeze.
- **Duplicate search:** recorded bounded searches covered current D5, pinned
  mathlib, exact atom references, receipts/reports, git history, and all 1,475
  refs; no exact complete-atom theorem or named carrier bridge was found.
- **Clause fidelity:** all seven clause groups are retained in the echo. The
  missing set is explicit and nonempty, so deposit is blocked.
- **Rendered-statement fidelity:** not run because no Lean/Scribe artifact was
  created. There is no new rendered statement that can drift.

Grader-trap accounting:

- **Witness vs universal:** the `N = 13` witness/certificate cannot discharge
  the universal at-most-three theorem, and the universal theorem cannot supply
  the five exact `N = 13` counts.
- **Instance vs general:** `N = 13` is not the Fibonacci-time universal family;
  `three_gap` for general `N` is not exact-two at Fibonacci time.
- **Conditional vs unconditional:** no missing bridge or certificate is moved
  into a hypothesis; doing so would weaken the unconditional atom.
- **Pointwise vs operator:** not applicable; no operator-valued conclusion is
  proposed.
- **Proof-internal vs addressable statement:** the private
  `log_phi(phi^n)=n` lemma supports an addressable scale-shift theorem but is
  not a continuous-group collapse. Likewise private `fullGap_spectrum` proves
  the pointwise two-length fact internally; the public addressable outcomes are
  `golden_full_gap_counts` and the gap-word theorems, still on the tower carrier.
- **Multi-clause residue names:** decisive. One atom ID owns all multiplication,
  addition, geometry, and certificate clauses; no single existing GID names
  the complete conjunction.
- **Mechanism vs outcome:** the tower results are genuine exact-two outcomes,
  not merely suggestive machinery. Without the collapse and carrier bridges,
  however, they do not prove the source's Phase-carrier outcome.

## Unreached commands and final disposition

`make lean`, `make emit`, `make deposit`, `make preflight`, `make cover`, and
`make pr-open` were not run. The scoped builds already verified the exact
reusable modules, while the workflow requires stopping before artifact
creation and ceremony when clause fidelity has a nonempty missing set.
`make preflight` is not a report-only check and would not cure the mathematical
gap. No GID exists for the complete atom.

The atom remains `open`. The dispatcher may separately bind already-covered
clauses only if the digestion model later provides a legitimate atom split;
this producing lane does not perform ledger surgery and does not partially
cover the existing coupled atom.

Ledger balanced: yes. The only intended worktree change is this report.
