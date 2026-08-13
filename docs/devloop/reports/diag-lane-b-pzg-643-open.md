# Diagonal Lane B: 6.43 Open Report

Outcome: open, with no formalization deposit.

This report records the isolated lane `harness/diag-formalize-b` at
`/Users/mstudio3/trureturing-diag-formalize-b`. Before selecting this atom,
the lane fetched and merged `origin/dev` at
`2a087760bcc2814fa46235252f0c6320122828ad`; the lane merge commit is
`7112f02ff27152bfa65d100a798f352f6c3d1958`.
`git merge-base --is-ancestor origin/dev HEAD` exited `0`, and the worktree
was clean before this report was added.

## Atom and authoritative statement

- Atom ID: `pzg-residual-49aad85920afca41580bd9b0a2bac6309cd6930d3f167f277a1f8cdba8835130`
- CAS reference: `sha256:49aad85920afca41580bd9b0a2bac6309cd6930d3f167f277a1f8cdba8835130`
- Source: `docs/develop/theory/PZG_BEDC.md`, `remark/6.43`
- Source ID: `pzg-v170`; atomizer: `pzg-v1`; AST path: `remark/6.43`
- Claim class: concrete finite-word classification plus exact golden capacity,
  Witt row identities, and a parity-to-chirality structural conclusion.
- `make show-atom ATOM_ID=pzg-residual-49aad85920afca41580bd9b0a2bac6309cd6930d3f167f277a1f8cdba8835130`
  exited `0`.
- `show-atom` reported `status=match` for raw, normalized, and CAS SHA-256
  values.

The authoritative text copied from the successful `show-atom` output is:

> **评注 6.43(窗口—同余翻译机)**〔semantic〕。四词 {1},{3},{4},{2,4} 是分类——a = 1 纤维于内部方向之**完全窗口覆盖**(b ∈ {0,1,2,3} 恰一次,截止非循环):窗口型,非同余型(评注 6.29 之二分)。"与 mod 2² 之关系"的精确判定:**4 非模而是容量 ⌊φ³⌋;然 mod 2 为真**——Witt 提取除以 (1 − v²) 型除子,窗口和 (1 − v^L)/(1 − v) 遇 2 ∣ L 则整除截止(L = 4,a = 1 行有限),遇 2 ∤ L 则无穷交替(L = 3,b = 1 行之 (−1)^k 恰为 ℤ/2 非平凡特征)。**Witt 反演由此显形为一台把窗口型数据翻译为同余型模式的机器**:评注 6.29 判然两分之两型,于此首次被一台机器架桥;级联手性(评注 6.41)之算术根源即窗口长之奇偶——四偶三奇。

## Statement echo

The atom has three independently testable unresolved groups. Meaning is
preserved only by retaining the complete atom as open; no clause is dropped or
weakened in this accounting.

1. **Complete four-word window and capacity group.** A faithful declaration
   needs a formal carrier for the atom's admissible words, definitions of the
   two fiber coordinates `a` and `b`, and a proof that the `a = 1` fiber is
   exactly the four distinct words `{1}`, `{3}`, `{4}`, and `{2,4}` with
   `b = 0,1,2,3` occurring exactly once. It must also prove that this four is
   the window capacity `floor(phi^3)`, not a residue-class cardinality. The
   repository's `GoldenFiberCoordinates` defines integral Beatty coordinates,
   but it neither defines the word fiber nor proves its support, cardinality,
   or complete coverage. No declaration proving `floor(phi^3) = 4` was found.
2. **Witt even-termination/odd-alternation group.** A faithful declaration
   needs the bivariate Witt exponent family `e_(a,b)`, its extraction from the
   word generating series, the `a = 1` row identity obtained through the
   `(1-v^2)` divisor, and the `b = 1` all-orders formula
   `e_(k,1) = (-1)^k` for every `k >= 2`. It must connect these formulas to
   the general quotient `(1-v^L)/(1-v)` and prove the even-window termination
   and odd-window infinite alternation cases. `BivariateWordSeries` proves
   only the coefficientwise self-substitution of the raw word series; it does
   not define a logarithm, Moebius/Witt inversion, or `e_(a,b)`.
3. **Parity translation and chirality group.** A faithful declaration needs a
   common theorem showing that Witt inversion maps finite window data to the
   parity-controlled congruence pattern, with length four producing the finite
   row and length three producing the nontrivial `Z/2` character. It then must
   identify this parity asymmetry with the cascade chirality asserted in the
   source. The repository has no common definition joining window capacity,
   Witt rows, and chirality. Generic parity and alternating-series lemmas do
   not supply this bridge.

The atom's phrase “4 is not modulus” also cannot be covered by
`FixedModulusNoncongruence.deficit_not_determined_by_fixed_modulus`. That
theorem concerns the normalized golden-addition deficit as a function of two
natural inputs. This atom concerns the cardinality and support of one Witt
fiber. The mathematical objects and conclusions are different.

## Library search trace

The following searches were run after syncing the lane.

```text
rg -n "theorem deficit_not_determined_by_fixed_modulus|theorem bookkeeping_series_self_functional_equation|theorem golden_fiber_coordinates|theorem alternating_pole_coefficients" D5 Library --glob '*.lean' --glob '*.md'
```

Exit `0`. Four nearby declarations were found:

- `D5/S1/Recurrence/BivariateWordSeries.bookkeeping_series_self_functional_equation`
- `D5/S1/Words/GoldenFiberCoordinates.golden_fiber_coordinates`
- `D5/S1/Deficit/FixedModulusNoncongruence.deficit_not_determined_by_fixed_modulus`
- `D5/S3/Analytic/AlternatingPoleCoefficients.alternating_pole_coefficients`

All four modules have active Freeze events. Their exact roles are respectively
raw word-series substitution, Beatty coordinate formulas, noncongruence of a
different deficit function, and the generic coefficient formula for a pole at
minus one. None states the atom's assembled result.

```text
rg -n "Witt|witt|Möbius|Mobius|plethystic|log.*extract|extract.*log" D5 Library Blueprint Evidence --glob '*.lean' --glob '*.md' --glob '*.cs' --glob '*.json'
```

The relevant hits were frontier/source prose and the raw bivariate word
series. No Lean definition of the atom's Witt exponent array, row extraction,
or all-orders `e_(k,1)` identity was found.

```text
rg -n "full.*window|complete.*window|fiber.*card|card.*fiber|capacity.*golden|floor.*goldenRatio.*3|goldenRatio.*3.*floor|four.*word|window.*parity|parity.*window|chirality" D5 Library Blueprint Evidence --glob '*.lean' --glob '*.md' --glob '*.cs' --glob '*.json'
```

No complete `a = 1` word-fiber enumeration, `floor(phi^3) = 4` theorem, or
capacity-parity-to-chirality theorem was found. Generic finite-fiber and
observer-window hits use unrelated carriers.

```text
rg -n "oneSubPow|geom.*sum|sum_geometric|invOneSub|coeff_rescale" .lake/packages/mathlib/Mathlib/RingTheory/PowerSeries D5/S3/Analytic --glob '*.lean'
```

Pinned mathlib supplies general power-series inversion and coefficient tools.
The repository wrapper `AlternatingPoleCoefficients` gives coefficients
`(-1)^n * choose(degree+n,degree)` for powers of `(1+X)^-1`. Neither mathlib
nor the wrapper identifies those coefficients with the atom's Witt row or
proves the finite even-window branch.

The latest actual formalization template inspected was commit
`9da126e6d795a4b01d442020b41b9724a6a2b578`, which added a Lean module and
its Blueprint `.scribe.cs` source while also registering a new domain. No
formal artifacts were created here because the complete statement echo exposed
dependencies that the library search did not supply, so a faithful declaration
could not be proposed without assumptions or omitted clauses.

## Failed approaches and diagnostics

- **Cover with `BivariateWordSeries`:** rejected. A raw combinatorial
  functional equation is prior input to Witt inversion, not the requested row
  extraction, finite termination, or infinite alternation result.
- **Cover with `GoldenFiberCoordinates`:** rejected. The coordinate formulas
  do not enumerate the `a = 1` word fiber or establish its four-element
  support and exact internal coordinates.
- **Cover the “not modulus” phrase with `FixedModulusNoncongruence`:** rejected
  because it proves a statement about the golden-addition deficit, not the
  source of the Witt fiber's cardinality.
- **Cover the odd row with `AlternatingPoleCoefficients`:** rejected. The
  generic coefficient sequence has no proved equality to `e_(k,1)` and says
  nothing about the even length-four termination.
- **Conjoin the four existing declarations:** rejected. Their carriers are
  not linked by any theorem, so conjunction would collect prerequisites and
  analogies rather than prove the atom.
- **Define abstract Witt rows and assume the extraction identities:** rejected
  as a hypothesis restatement that would fail the non-hollowness gate.
- **Edit the neighboring modules:** independently prohibited because all four
  have active Freeze events, and adding declarations would change their frozen
  declaration sets.
- **Scoped Lean verification:**
  `lake build D5.S1.Recurrence.BivariateWordSeries D5.S1.Words.GoldenFiberCoordinates D5.S1.Deficit.FixedModulusNoncongruence D5.S3.Analytic.AlternatingPoleCoefficients`
  exited `0` and reported `Build completed successfully (8578 jobs)`, with
  only pre-existing long-line warnings in dependencies.

## Fidelity gate

- Conclusion substance: no new theorem was proposed; no `True`, definition-only
  wrapper, or hypothesis restatement was deposited.
- Hypothesis satisfiability: not applicable because no candidate declaration
  was introduced. The absent Witt and word-fiber carriers are explicitly
  named above.
- Domain inhabitance: not applicable because no new domain was introduced.
- Proof substance: blocked by the missing Witt extraction and common
  capacity/parity/chirality bridge; existing prerequisites were not presented
  as the missing theorem.
- Duplicate search: complete, with commands, hits, and signature distinctions
  recorded above.
- Clause fidelity: all three unresolved groups and their independently
  testable subclaims remain in the open accounting; the dropped-or-weakened
  set is empty.
- Rendered-statement fidelity: not run because no Lean or Scribe artifact was
  created.
- Grader traps: prerequisite-vs-result, same-number-vs-same-object,
  finite-vs-all-orders, and analogy-vs-identity all block the partial wrappers.

`make lean`, `make deposit`, `make preflight`, `make cover`, receipt emission,
and coverage alignment were not run. The formalization workflow stops before
deposit when the authoritative atom cannot be mapped without omitted or
assumed clauses. No file under `Meta/Digestion/**`, `Golden/Frozen/**`, or a
formalization-receipt path was edited.

## Verdict

The atom remains **open**. The library contains useful raw word-series,
Beatty-coordinate, generic alternating-coefficient, and deficit-noncongruence
theorems, but it lacks the exact four-word fiber enumeration, the capacity
identity `floor(phi^3) = 4`, the Witt exponent and row extraction definitions,
and the parity-to-chirality bridge needed to connect them faithfully.

Ledger balanced: yes. No formalization deposit was made.
