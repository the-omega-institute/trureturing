---
bibkey: kimihiro2026robin1984
authors: Jonas Whidden
year: 2026
title: "Robin1984: the actual Robin, colossally abundant and Lagarias equivalences"
doi: null
url: https://github.com/kimihiro64/Robin1984/tree/acab1a31f31e0499518a4416b63281e0b4838f9c
claim: "The pinned source proves actual Mathlib RH equivalent to the strict actual divisor-sum inequality for every natural n > 5040, with actual standard-three-axiom Comparator, NanoDa and Lean replay evidence; its unchanged arithmetic carrier compiles locally, while the full proof closure is not yet ported."
strata_touched:
  - D5/S3/Arith/Robin/PrimePrefixMobiusDirectedAbel
  - D5/S3/Arith/Robin/PrimePrefixOriginalA
license: Apache-2.0
triage: anchor
---

# Robin's criterion with upstream proof acceptance

Source repository [kimihiro64/Robin1984](https://github.com/kimihiro64/Robin1984/tree/acab1a31f31e0499518a4416b63281e0b4838f9c),
immutable main commit `acab1a31f31e0499518a4416b63281e0b4838f9c`.
The pinned [CITATION.cff](https://github.com/kimihiro64/Robin1984/blob/acab1a31f31e0499518a4416b63281e0b4838f9c/CITATION.cff)
names Jonas Whidden as the formalization author. The repository account name
does not establish an additional personal author. The mathematical Robin
equivalence belongs to Guy Robin (1984), its converse uses Nicolas--Landau,
and the separate elementary criterion belongs to Jeffrey C. Lagarias.

## Exact mathematical supply

The pinned [Definitions.lean](https://github.com/kimihiro64/Robin1984/blob/acab1a31f31e0499518a4416b63281e0b4838f9c/Robin1984/Arithmetic/Definitions.lean)
sets `sigmaOneNat n := ArithmeticFunction.sigma 1 n` and uses Mathlib's
`Real.eulerMascheroniConstant`. Its predicate is exactly

$$
\sigma_1(n)<e^\gamma n\log\log n,
\qquad n\in\mathbb N.
$$

`Robin1984.Core.NativeRobinInequalityAll` universally quantifies this strict
inequality over every natural `n` with `5040 < n`.
The theorem
`Robin1984.riemannHypothesis_iff_nativeRobinInequalityAll` in
[Equivalence.lean](https://github.com/kimihiro64/Robin1984/blob/acab1a31f31e0499518a4416b63281e0b4838f9c/Robin1984/Equivalence/Equivalence.lean)
is the unconditional equivalence between that predicate and Mathlib's actual
`RiemannHypothesis`. The imported Mathlib definition concerns zeros of the
actual `riemannZeta`, excludes the negative even trivial zeros and `s = 1`,
and requires real part `1/2`. There is no project replacement RH predicate.

The forward proof partitions the integer domain at `Real.log (n : Real) = 74500`.
[FiniteComplete.lean](https://github.com/kimihiro64/Robin1984/blob/acab1a31f31e0499518a4416b63281e0b4838f9c/Robin1984/Finite/FiniteComplete.lean)
proves the literal Robin inequality unconditionally when `5040 < n` and
`log n < 74500`. Exact startup certificates cover `5040 < n < 720720`;
the remaining finite logarithmic interval is covered by certified tangents.
[LargeHeightRobin.lean](https://github.com/kimihiro64/Robin1984/blob/acab1a31f31e0499518a4416b63281e0b4838f9c/Robin1984/Equivalence/LargeHeightRobin.lean)
proves the large range under an explicit actual RH assumption. The reverse
proof in
[NicolasLandauRobinBridge.lean](https://github.com/kimihiro64/Robin1984/blob/acab1a31f31e0499518a4416b63281e0b4838f9c/Robin1984/NicolasLandau/NicolasLandauRobinBridge.lean)
uses the proved actual Nicolas negative oscillation under failure of RH.

The three public proved endpoints in
[Solution.lean](https://github.com/kimihiro64/Robin1984/blob/acab1a31f31e0499518a4416b63281e0b4838f9c/Solution.lean)
are `Robin1984.robin_inequality_iff_riemannHypothesis`,
`Robin1984.riemannHypothesis_iff_colossallyAbundant_robin` and
`Robin1984.riemann_hypothesis_iff_lagarias_elementary_criterion`.
The colossally abundant endpoint restricts the same Robin inequality to the
actual extremizers of the parameterized abundancy ratio. Each endpoint is an
equivalence; it does not establish either side unconditionally.

## Actual verification and dependency boundary

The saved authenticated GitHub API results identify
[CI run 34748103247](https://github.com/kimihiro64/Robin1984/actions/runs/34748103247)
with the exact source commit above and successful Lean build and
[statement-against-solution job 103700837549](https://github.com/kimihiro64/Robin1984/actions/runs/34748103247/job/103700837549).
The complete saved job log exports the three public endpoints at line 1623,
then records actual NanoDa acceptance, actual Lean default-kernel acceptance
and `Your solution is okay!` at lines 1624--1628. This is a recorded upstream
run, not a new local replay of that proof closure.

The pinned [comparator.json](https://github.com/kimihiro64/Robin1984/blob/acab1a31f31e0499518a4416b63281e0b4838f9c/comparator.json)
permits only `propext`, `Quot.sound` and `Classical.choice`, and enables NanoDa.
The pinned
[verification script](https://github.com/kimihiro64/Robin1984/blob/acab1a31f31e0499518a4416b63281e0b4838f9c/scripts/verify-comparator.sh)
requires `enable_nanoda` to be exactly true and fixes Comparator at
`68a064109f01c08f47c8edc9f51d6a2bbffaa188`.
The actual Comparator implementation was read:
[Util.lean](https://github.com/leanprover/comparator/blob/68a064109f01c08f47c8edc9f51d6a2bbffaa188/Comparator/Util.lean)
traverses types and proof values, including opaque values;
[Axioms.lean](https://github.com/leanprover/comparator/blob/68a064109f01c08f47c8edc9f51d6a2bbffaa188/Comparator/Axioms.lean)
recursively rejects unpermitted axioms reachable from the target theorems;
[Main.lean](https://github.com/leanprover/comparator/blob/68a064109f01c08f47c8edc9f51d6a2bbffaa188/Main.lean)
checks statement/definition agreement and these axioms before NanoDa and Lean
replay. An error aborts that sequence. NanoDa also receives
`unpermitted_axiom_hard_error = true`.

The saved own-source import closure contains 149 modules (1,517,626 bytes)
for `Equivalence.lean` and 167 modules (1,742,374 bytes) for `Solution.lean`.
Their Git blobs and byte hashes were checked. A comment/string-stripped
lexical scan found no proof-hole, custom-axiom or unsafe/native-evaluation
tokens in those own closures. The one `opaque` is an initialized
`CA5040EventsPackage` with literal actual events and an `rfl` equality.
The separate `Challenge.lean` contains its three intended statement holes
and is not imported by the solution proof.

These are source import closures, not minimal proof-constant closures or a
full manual review of all proof bodies. Their five external PNT module
seeds lead to 99 modules (2,350,044 bytes) in the exact fork
`kimihiro64/PrimeNumberTheoremAnd` at
`f8f58c749d6cde8a641348fcd5e4702993651cd6`.
That imported fork closure contains 13 literal `sorry` declarations in four
modules. The actual target axiom enforcement and dual-kernel acceptance
exclude those placeholders from the three selected theorem proofs; they do
not certify every declaration in those imported modules. No complete
third-party source audit or new local `#print axioms` of the three upstream
endpoints is claimed.

## Local entry and intended consumers

Upstream uses Lean `v4.33.1`, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, the PNT fork above, leancert
`621a43d7cf21f87872392a01e874f2f1dbddc926`, PrimeCert
`916ee9c35a57af128d5089a69172415051e700ca` and LeanArchitect
`d9013cc08bd2b5483e837368dfa4cc7ead92a5c2`. The complete manifest is retained
with the source snapshot.

The unchanged `Arithmetic/Definitions.lean` and a transient `Iff.rfl`
check of its literal all-`n > 5040` statement compiled with actual exit 0
under this repository's Lean `v4.33.0`, Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`, `--trust=0` and
`debug.skipKernelTC=false`. The receipt is
`robin1984-local-carrier-native36/receipt.json`; both upstream and local
definition bytes have SHA256
`cac28c82777fc92ea8ec4e18eed1b29d2b2a361e40f3fe3c1f3e4d9c8e5b1b88`.
This proves compatibility of the arithmetic statement. The 149-module
equivalence proof and its external closure have not been ported or given
local canonical acceptance. No D5 wrapper was retained for the transient
definitional check.

The `strata_touched` entries name existing local Robin research targets.
`PrimePrefixMobiusDirectedAbel` retains the actual harmonic Mobius prefix,
same finite window and signed anchor/terminal, with prefix estimates as
caller hypotheses. `PrimePrefixOriginalA` proves the original two-piece
Phi constant's integrability and strict bound below `1/2`. Neither currently
imports the external equivalence. Connecting the original signed arithmetic
tail to the literal all-integer Robin predicate remains a mathematical
obligation; a locally accepted equivalence would then supply a precise RH
endpoint. The external unconditional finite certificates offer an additional
concrete source for replacing repeated finite-range work.

## Attribution and licence

The complete upstream root
[Apache-2.0 LICENSE](https://github.com/kimihiro64/Robin1984/blob/acab1a31f31e0499518a4416b63281e0b4838f9c/LICENSE)
was read and retained: 11,357 bytes, Git blob
`261eeb9e9f8b2b4b0d119366dda99c6fd7d35c64`, SHA256
`c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4`.
The complete pinned repository tree has no root or proof-path NOTICE file.
The exact PNT fork carries the same root licence, and its added xi-divisor
source retains Matteo Cipollina's 2026 author/copyright header. Upstream
[LICENSING.md](https://github.com/kimihiro64/Robin1984/blob/acab1a31f31e0499518a4416b63281e0b4838f9c/LICENSING.md)
does not relicense mathematical papers or third-party dependencies.
This note distributes no transplanted upstream proof code. Any later source
port must retain the applicable licence, original notices, immutable source
pin and description of modifications.
