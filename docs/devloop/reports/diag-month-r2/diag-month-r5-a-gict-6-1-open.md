# Diagonal Month R5 Lane A: GICT Theorem 6.1 Open Report

Outcome: `open`, with no formalization deposit and no partial cover.

The selected atom asserts one exact sequence for every prime set `S`, then an
all-prime specialization identifying the middle term with the Pontryagin dual
of `Q` and the kernel with the profinite integers. The synchronized repository
contains four substantial but strictly partial components: an element-level
exact sequence indexed by every positive modulus, an all-prime exact sequence,
an additive equivalence between its kernel and the product of all prime-adic
integer rings, and a classification of characters *of* the universal solenoid
by the rationals. It contains neither an arbitrary-`S` solenoid nor an explicit
topological-group equivalence from the universal solenoid to
`PontryaginDual Q`. The character theorem has the opposite dual direction. The
all-prime kernel identification is algebraically structured, but no checked
declaration makes it continuous or a homeomorphism. Binding these partial
results to the atom would still drop or weaken source clauses.

No Lean, Blueprint, Scribe, Evidence, digestion receipt, coverage record,
frozen event, or generated projection was edited. No deposit, cover, push, or
pull request was attempted.

## Environment and synchronized baseline

The assigned isolated lane is:

```text
worktree = /Users/mstudio3/trureturing-diag-month-r4-a
branch = harness/diag-month-r5-a
```

The lane began clean at
`935a9fed418bc963c1e177c594dc149ee7f0ed8d`. After the shared base advanced,
the dispatcher required synchronization before any edit:

```sh
git merge --ff-only origin/dev
```

Exit `0`; this first, historical synchronization fast-forwarded the clean lane
to:

```text
HEAD = 901b052ad1d1f0f2e422be1af24276c38d532ce7
origin/dev = 901b052ad1d1f0f2e422be1af24276c38d532ce7
```

`pwd -P` and `git rev-parse --show-toplevel` both returned the assigned
worktree. `git merge-base --is-ancestor origin/dev HEAD` exited `0`, and
`git status --short` was empty before this report was added.

`make help` was read as the live door catalogue. On the synchronized base,
`make dotnet` exited `0` with zero warnings and zero errors. The base advance
added `D5/S3/Weil/ZetaBridge/ConvolutionSquareCriticalLine.lean`; the first
post-advance `digest-status` correctly failed closed with:

```text
DIGEST_STATUS_INVALID Raw Lean report is missing modules:
D5/S3/Weil/ZetaBridge/ConvolutionSquareCriticalLine.lean
```

`make lean-report` then exited `0`, refreshing the canonical report from its
content-addressed cache. Only after that refresh was atom status trusted.

After the report was committed, `origin/dev` advanced through PRs #1704 and
#1705 to `4436226aac7879b3469c5c343110779c9901501b`. Because the report commit
was then branch-local, the synchronization used the non-destructive merge
door rather than `--ff-only`:

```sh
git merge --no-edit origin/dev
```

It completed without conflict as merge commit
`d91d97f641a9211595ee84b8df25415b30c5a241`. PR #1704 added the unrelated
`XiProductEndpointLimits` result; PR #1705 added the unrelated
`GoldenFiberPrefixBound` deposit and receipt.

For this correction, the clean report branch again ran:

```sh
git merge --no-edit origin/dev
```

It completed without conflict as
`f817215721616125663b058f3e46d41e78d6d3c4`, whose second parent and synchronized
content base at that point were:

```text
origin/dev = a6dcb9be36dc5b929e4b96fe5310df95d78f3c75
merge-base(origin/dev, HEAD) = a6dcb9be36dc5b929e4b96fe5310df95d78f3c75
```

The additional PRs #1707-#1709 add `MellinDilationFlow`,
`ConvolutionSquareOffLineOrbits`, and `ConvolutionSquareOrbitBounds`, plus
their mirrors/freeze or backfill updates. Statement inspection and a focused
search of those three incoming Lean modules found no `UniversalSolenoid`,
`PontryaginDual`, `HiddenAddress`, or `hiddenKernelAddEquiv` occurrence.

Before committing this correction, `origin/dev` advanced through PRs #1710 and
#1711. A final non-destructive
`git merge --no-edit 5b69e67602e7cc960dc63a110ab1766fb64b19ec`
completed without conflict as `8225ad19073854a9f16b3098066f844a9470fdac`.
Its second parent and the synchronized content base at that point were:

```text
origin/dev = 5b69e67602e7cc960dc63a110ab1766fb64b19ec
merge-base(origin/dev, HEAD) = 5b69e67602e7cc960dc63a110ab1766fb64b19ec
```

PR #1710 adds `PriceFaceOrder` and its domain registration; PR #1711 adds
`SignedPrimeLogDensity`. Statement inspection and a focused search of both
incoming Lean modules and their mirrors found no selected-atom carrier or
topological upgrade. The only broad search hit was the unchanged, pre-existing
`Solenoid` entry in `Meta/domains.yaml`; the incoming YAML hunk registers only
`ResourceOrder`. None of these seven later PRs changes a clause disposition
below.

After the history-audit correction was committed, `origin/dev` advanced through
PR #1713. A final non-destructive
`git merge --no-edit 88fb4a9cc3d56cf08747a948ffc014af57a0e4cd`
completed without conflict as `cf3f73d6651d70184c572993d6ea6db5f656ed9c`.
Its second parent and the synchronized content base at that point were:

```text
origin/dev = 88fb4a9cc3d56cf08747a948ffc014af57a0e4cd
merge-base(origin/dev, HEAD) = 88fb4a9cc3d56cf08747a948ffc014af57a0e4cd
```

PR #1713 adds `WideVacuumBand`, its Scribe source and Blueprint projection,
seven freeze records, and one formalization receipt for the different atom
`pzg-residual-aa45f85f...`. The theorem constructs arbitrarily wide bands in a
lookup-program spectrum. A focused search across all eleven incoming paths
exited `1` with no `UniversalSolenoid`, `PontryaginDual`, `HiddenAddress`,
`hiddenKernelAddEquiv`, solenoid, profinite, p-adic, selected-atom, or exact-
sequence occurrence. This deposit changes no clause disposition below.

After the report-base refresh was committed, `origin/dev` advanced through PR
#1714. A final non-destructive
`git merge --no-edit 4551a412d3dfbf5bcaa25755e34bbf8481c1a3e8`
completed without conflict as `2fa9ec70503067aa7995a93afd9d1edad827fc4d`.
Its second parent and the synchronized content base at that point were:

```text
origin/dev = 4551a412d3dfbf5bcaa25755e34bbf8481c1a3e8
merge-base(origin/dev, HEAD) = 4551a412d3dfbf5bcaa25755e34bbf8481c1a3e8
```

PR #1714 adds only `GoldenDesubstitutionClosedForms.lean` and its Scribe and
Blueprint mirrors. Its two public theorems give expansion- and contraction-face
logarithmic closed forms for golden desubstitution. A focused search across all
three incoming paths exited `1` with no selected-atom, solenoid,
Pontryagin-dual, profinite, p-adic, kernel-equivalence, or exact-sequence
occurrence. It changes no clause disposition below.

The R5 replay began after `origin/dev` had been fetched at
`f94e87a89fd0a681936647038edf285f21eee916`. The exact non-destructive merge

```sh
git merge --no-edit f94e87a89fd0a681936647038edf285f21eee916
```

completed without conflict as `a3c33f20b5604eb6b46f87c812ec111f765669b2`.
Its second parent and pinned replay content base are:

```text
pinned replay base = f94e87a89fd0a681936647038edf285f21eee916
merge-base(f94e87a, HEAD) = f94e87a89fd0a681936647038edf285f21eee916
```

PR #1715 adds `PrimeLogIndependence.lean` and its Scribe and Blueprint mirrors,
and updates only PZG remark 27.119's backfill record. The new theorem rules out
nontrivial finite rational relations among prime logarithms; the PZG update adds
that theorem's GID and removes its matching unresolved subitem. PR #1716 adds
`GoldenContractionRadicalBound.lean` and its two mirrors; its public theorems
bound a golden-desubstitution contraction error using `primeRadical`.

An initial broad `prime.adic` text pattern matched only the unrelated
`primeRadical` identifier. The refined focused search across all seven incoming
paths exited `1` with no selected-atom, solenoid, Pontryagin-dual, profinite,
p-adic, kernel-equivalence, or exact-sequence occurrence. Neither PR changes a
clause disposition below, and the selected GICT backfill remains untouched.

During that preliminary report refresh, the shared `origin/dev` ref advanced
to `e18dd230ad6bcb900ee96f3a48c3d32d0bffaafd`. At that historical point this
lane performed no fetch and did not merge the later base, which was not then an
ancestor of the lane. That movement invalidated the f94 quiet-window gate
claim, but it did not change the pinned `f94e87a8` content audit.

On the pinned `f94e87a8` tree, `make lean-report` exited `0`, producing:

```text
input_address = sha256:a869ce251abcc700b0770c03c20bd8c6a3c240a1a42c87165495b5a5f1f92e55
report_sha256 = e71f3c30b659d7e260d814de12caeac6e5a0e28f16cb034ab55bbaabf4940d29
```

The final R5 synchronization began with the shared ref already at the exact
target, without another fetch. The preserved report edit was carried through
this exact non-destructive merge:

```sh
git merge --no-edit 9014d6103a180f6347cb6d092b078ca1560958cf
```

Exit `0`; it completed without conflict as
`4e6722d9c48fc0838bab0b0e072e8f7cd159a5f2`. Its parents and final content
base are:

```text
parents = a3c33f20b5604eb6b46f87c812ec111f765669b2 9014d6103a180f6347cb6d092b078ca1560958cf
origin/dev = 9014d6103a180f6347cb6d092b078ca1560958cf
merge-base(origin/dev, HEAD) = 9014d6103a180f6347cb6d092b078ca1560958cf
```

The `f94e87a8..9014d610` delta contains 270 changed paths, 9,884 insertions,
and 55 deletions. Its large ingestion component registers the independent
`qdo-v1` source and atomizer dialect, adds the quantitative-diagonalization
reference volume, 114 CAS atoms, and 115 source/backfill paths. The source and
all of those residual records are QDO-addressed, not GICT theorem 6.1
coverage.

The tooling component batches revision blob reads through `git cat-file
--batch` and rejects newly added frozen-ledger events whose Git anchors cannot
be resolved. The content component adds six independent Lean modules:
`GoldenMidlineFactorization`, `AffordableRegionAgreement`,
`SearchableWindowDecision`, `GoldenSubstitutionOrbit`,
`BackwardShiftOperator`, and `FourPointPowerDefect`, with their mirrors and
seven freeze events. Four new formalization receipts bind three PZG atoms and
one different GICT atom. In particular:

```text
incoming GICT receipt atom = gict-residual-d04f41c3612d0baaf0b2430e263e09a99103c4bb8eacd28a6dbe85baa4d77cdd
incoming GICT primary GID = D5/S3/Zeros/ToySpectrum/FourPointPowerDefect.four_point_power_defect_eq
selected atom = gict-residual-5db40deeb77603206799812f973d4eee90041979570108b72914623feb17810a
```

The `d04f...` receipt is therefore not a receipt for the selected `5db40...`
atom. A full-content search over all 270 incoming paths for the exact selected
ID exited `1`. The carrier search across the same path set found only the prose
phrase `solenoid path orbit classification` in the new QDO reference volume;
it found no `UniversalSolenoid`, `PontryaginDual`, `HiddenAddress`,
`hiddenKernelAddEquiv`, profinite, p-adic, or exact-sequence carrier. These
changes do not alter any selected-atom clause disposition below.

On the final merged tree, a fresh bare `make lean-report` exited `0` and
produced:

```text
input_address = sha256:bdb5001081468f123f50a4dd126daa1fa36e05a16a101106c6d883a60cd033eb
report_sha256 = 6f04896a66cee2f912b6feaf1f52f662badbd4dbf20b444a8b07843344ec73d8
```

## Atom and authoritative statement

- Atom ID:
  `gict-residual-5db40deeb77603206799812f973d4eee90041979570108b72914623feb17810a`
- Source ID: `gict-v3.6`
- Source path: `docs/develop/theory/GICT.md`
- AST path: `theorem/6.1`
- Atomizer: `gict-v1`

The authoritative command was run again after synchronization:

```sh
make show-atom \
  ATOM_ID=gict-residual-5db40deeb77603206799812f973d4eee90041979570108b72914623feb17810a
```

Exit `0`. It reported matching raw, normalized, and CAS hashes:

```text
raw_sha256=sha256:5db40deeb77603206799812f973d4eee90041979570108b72914623feb17810a
normalized_sha256=sha256:5db40deeb77603206799812f973d4eee90041979570108b72914623feb17810a
cas_ref=sha256:5db40deeb77603206799812f973d4eee90041979570108b72914623feb17810a
status=match
```

The complete authoritative raw text is:

```text
**定理 6.1(prime-register 正合列)**〔定理·典〕。**0 → ∏_{p∈S}ℤ_p → Σ_S → 𝕋 → 0**;S=ℙ 时 Σ=ℚ̂,核 ℤ̂。
```

After `make lean-report`, the exact status query was:

```sh
dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj \
  --configuration Release --no-build -- digest-status --json
```

Filtering its result by the atom ID gives:

```text
alignment = seen
migration = residual
truth = open
deletable = false
gaps = [{ code = coverage-gid-missing, detail = <this atom ID> }]
```

The selected-atom formalization-receipt and prior-report query, excluding this
report itself, exited `1` with no hit:

```sh
rg -n -F \
  'gict-residual-5db40deeb77603206799812f973d4eee90041979570108b72914623feb17810a' \
  Meta/Digestion/formalizations docs/devloop/reports/diag-month-r2 \
  --glob '!diag-month-r5-a-gict-6-1-open.md'
```

The canonical residual-open record is instead addressed by its filename:

```text
Meta/Digestion/backfill/gict-v3.6/residual-open/
gict-residual-5db40deeb77603206799812f973d4eee90041979570108b72914623feb17810a.yaml
```

Its raw, normalized, and CAS fingerprints all match the selected atom. Its
`coverage_gids`, `receipts.coverage`, and `receipts.scribe` fields are empty.
Thus a canonical residual-open backfill occurrence exists, but no formalization
or executed coverage/Scribe receipt exists.

The retained-history searches included the backfill tree and its exact path:

```sh
git log --all --oneline \
  -S'gict-residual-5db40deeb77603206799812f973d4eee90041979570108b72914623feb17810a' \
  -- D5 Blueprint Meta/Digestion/formalizations Meta/Digestion/backfill \
     docs/devloop/reports/diag-month-r2

git log --all --follow --oneline -- \
  Meta/Digestion/backfill/gict-v3.6/residual-open/\
gict-residual-5db40deeb77603206799812f973d4eee90041979570108b72914623feb17810a.yaml
```

The broad history may show report-only correction commits first because each
correction repeats the atom ID; `393c30be` is the original report addition.
Those report-history hits are not formalization or coverage events. The
exact-path history independently records canonical backfill ingestion and
migrations: `0f0edb92` introduced the per-atom residual record, with later
schema/path migrations at `201ecb7e`, `4eaedb39`, and `6178b8fa`. No
retained-history hit deposits or covers the selected atom.

## Clause-level statement echo

No source clause is dropped from this accounting.

| Authoritative clause | Required faithful Lean counterpart | Current evidence and disposition |
|---|---|---|
| `p in S` and `product_(p in S) Z_p` | A binder for an arbitrary set of primes `S`, a prime-indexed product restricted to `S`, and a definition of the corresponding middle object `Sigma_S` | Missing. Current solenoid carriers range over every positive modulus or every prime. No current-tree or all-ref declaration defining an `S`-indexed solenoid was found. |
| `0 -> product_(p in S) Z_p -> Sigma_S -> T -> 0` | Explicit injection and visible projection maps, injectivity of the first map, exactness at `Sigma_S`, and surjectivity onto the circle, uniformly in `S` | Missing at source generality. `congruence_solenoid_short_exact` proves this element-level shape only for compatible residues at all positive moduli. `universal_solenoid_profinite_exact` is all-prime only. |
| `S = P` | A specialization theorem connecting the arbitrary-`S` construction to the all-prime construction | Missing because there is no arbitrary-`S` carrier to specialize. An all-prime theorem alone cannot discharge a universally quantified prime-set clause. |
| `Sigma = Q-hat` | An explicit equivalence of the all-prime solenoid with `PontryaginDual Q = Hom(Q,T)`, with the algebraic and topological structure required by the source notation | Missing. GICT theorem 6.6 explicitly states `Hom(Q,T) = Q-hat`, so the dual direction is not ambiguous. The current `characterEquivRational` proves `PontryaginDual Sigma` is additively equivalent to `Q`; it does not prove `Sigma` is equivalent to `PontryaginDual Q`. |
| `kernel Z-hat` | Identification of the all-prime kernel with the profinite integers, equivalently the product of all `Z_p`, in a structure compatible with the exact sequence | Algebraically covered for the all-prime carrier. `HiddenAddress` abbreviates `forall p : Nat.Primes, Z_[p.1]`, and `D5.S3.Observer.HiddenFlow.StreamlineExistence.hiddenKernelAddEquiv` has type `HiddenAddress ≃+ UniversalSolenoid.projection.ker`. The remaining structured-kernel gap is topological: no declaration proves this additive equivalence or its inverse continuous, or packages it as a homeomorphism/topological-group equivalence. |

The missing-clause set is therefore nonempty: arbitrary-`S` construction and
maps, uniform exactness, the `S = P` specialization bridge, the explicit
`UniversalSolenoid` to `PontryaginDual Q` equivalence, and a topological upgrade
of the existing additive kernel equivalence. The arbitrary-`S` carrier and
exact sequence remain wholly absent; the all-prime result does not supply that
generality.

## Existing partial carriers and freeze boundary

The focused current-tree query was:

```sh
rg -n \
  'congruence_solenoid_short_exact|universal_solenoid_profinite_exact|continuous_solenoid_characters_are_rational|characterEquivRational|profiniteKernelEquiv|HiddenAddress|hiddenKernelAddEquiv' \
  D5 --glob '*.lean'
```

Exit `0`; it found only the following relevant public declarations:

- `D5/S1/Solenoid/ExactSequence.congruence_solenoid_short_exact`
  (`ExactSequence.lean:157`) proves injectivity, `Function.Exact`, and
  surjectivity for `CongruenceData`, whose coordinates range over every
  positive modulus. Its Scribe commentary expressly limits the claim to the
  element-level exact sequence and leaves topological duality open.
- `D5/S3/Factorization/SolenoidProfiniteKernel.profiniteKernelEquiv`
  (`SolenoidProfiniteKernel.lean:142`) is
  `UniversalSolenoid.projection.ker ≃ (forall p : Nat.Primes, Z_[p])`.
  `universal_solenoid_profinite_exact` (`:149`) asserts exactness,
  surjectivity, and only `Function.Bijective profiniteKernelEquiv`.
- `D5/S3/Observer/StreamlineTheorem.HiddenAddress`
  (`StreamlineTheorem.lean:19`) is the all-prime product
  `forall p : Nat.Primes, Z_[p.1]`.
  `D5/S3/Observer/HiddenFlow/StreamlineExistence.hiddenKernelAddEquiv`
  (`StreamlineExistence.lean:101`) upgrades the same kernel classification to
  `HiddenAddress ≃+ UniversalSolenoid.projection.ker`. Searches for that name
  together with `continuous` and `homeomorph` find no topological upgrade.
- `D5/S1/Dynamics/SolenoidCharacter.continuous_solenoid_characters_are_rational`
  (`SolenoidCharacter.lean:301`) classifies continuous characters of the
  universal solenoid. `characterEquivRational` (`:321`) packages
  `Character ≃+ Q`, where `Character = UniversalSolenoid ->_continuous+ T`.

All five modules carrying these components have active freeze records:

```text
Golden/Frozen/accepted/b9180e77...json -> D5/S1/Solenoid/ExactSequence.lean
Golden/Frozen/accepted/a5fb95bb...json -> D5/S3/Factorization/SolenoidProfiniteKernel.lean
Golden/Frozen/accepted/13667e24...json -> D5/S1/Dynamics/SolenoidCharacter.lean
Golden/Frozen/accepted/0d3173b6...json -> D5/S3/Observer/StreamlineTheorem.lean
Golden/Frozen/accepted/8dd16725...json -> D5/S3/Observer/HiddenFlow/StreamlineExistence.lean
```

The first three modules also have formalization receipts for three different
PZG atoms:

```text
pzg-residual-38bf584e... -> ExactSequence.congruence_solenoid_short_exact
pzg-residual-297e2147... -> SolenoidProfiniteKernel.universal_solenoid_profinite_exact
pzg-residual-e6eb2d21... -> SolenoidCharacter.continuous_solenoid_characters_are_rational
```

On the refreshed report all three PZG atoms remain `residual/open`, each with
`coverage-gid-missing`. These receipts neither cover the selected GICT atom nor
authorize adding declarations to the frozen modules. The Observer receipt
`observer-residual-41d280b2...` separately hosts
`StreamlineExistence.existsUnique_frozen_streamline_decomposition` and covers a
different premise/rigidity atom; it likewise supplies no selected-GICT-atom
coverage.

## Repository and pinned-mathlib searches

The exact current-tree distinctness query was:

```sh
rg -n \
  'UniversalSolenoid.*PontryaginDual|PontryaginDual.*UniversalSolenoid|PontryaginDual.*ℚ|ℚ.*PontryaginDual|Set Nat\.Primes|S : Set Nat\.Primes|S : Set ℕ|∀ p ∈ S' \
  D5 Blueprint/D5 --glob '*.lean' --glob '*.scribe.cs'
```

Exit `0` only because the broad `S` alternatives found unrelated finite-prime
sets in factorization, axis, arithmetic, and Weil modules. It found no
solenoid/Pontryagin-dual bridge and no arbitrary-prime-set solenoid.

The exact topology-boundary query was:

```sh
rg -n -i \
  'hiddenKernelAddEquiv|HiddenAddress.*UniversalSolenoid\.projection\.ker|UniversalSolenoid\.projection\.ker.*HiddenAddress|homeomorph|continuous.*hiddenKernel|hiddenKernel.*continuous' \
  D5 --glob '*.lean'
```

Exit `0` for the additive-equivalence definition and its algebraic uses, plus
unrelated homeomorphism text. It found no theorem asserting continuity of
`hiddenKernelAddEquiv` or its inverse and no homeomorphism built from it.

Pinned mathlib was searched directly:

```sh
rg -n -i 'solenoid' .lake/packages/mathlib/Mathlib --glob '*.lean'
```

Exit `1`; no hit.

```sh
rg -n \
  'PontryaginDual.*(Rat|ℚ)|(?:Rat|ℚ).*PontryaginDual|ProfiniteIntegers|UniversalSolenoid' \
  .lake/packages/mathlib/Mathlib --glob '*.lean'
```

Exit `1`; no specialization or solenoid carrier hit. The generic query

```sh
rg -n 'PontryaginDual' \
  .lake/packages/mathlib/Mathlib/Topology/Algebra/PontryaginDual.lean \
  .lake/packages/mathlib/Mathlib/Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean
```

found the generic definition, functorial map, topology/group instances, and
finite-abelian double-dual results only. It found no rational specialization.

The historical f94 replay had 1,560 refs. The final merged-tree census had
1,572, so this bounded all-ref query was repeated with the complete final ref
list and only Lean paths:

```sh
set -o pipefail
r5_refs=(${(f)"$(git for-each-ref --format='%(refname)')"})
git grep -n -h -E \
  'UniversalSolenoid.*PontryaginDual|PontryaginDual.*UniversalSolenoid|PontryaginDual.*ℚ|ℚ.*PontryaginDual|((abbrev|def|structure) [A-Za-z0-9_]*(Solenoid|solenoid).*(S :|\(S))|∏.*p.*∈.*S.*ℤ_\[)' \
  $r5_refs -- 'D5/**/*.lean' | sort -u
```

Exit `1`; no exact carrier or bridge hit. These text searches establish
addressable-library distinctness, not a global theorem of mathematical
nonexistence.

## Third-party Lean search

Third-party search was attempted because repository rule 11 requires the path
`D5 -> pinned mathlib -> third-party Lean ecosystem -> local proof`.

Loogle queries and results:

```text
query: "solenoid"
result: Found 0 declarations whose name contains "solenoid".

query: PontryaginDual
result: Found 23 declarations mentioning PontryaginDual; all were generic.

query: PontryaginDual Rat
result: Found 0 matching declarations.
```

LeanSearch's frontend ignores a GET query until JavaScript posts to `/search`.
The actual POST endpoint was therefore called with four queries:

```text
UniversalSolenoid
Pontryagin dual of the rational numbers
exact sequence solenoid profinite integers circle
S-adic solenoid for a set of primes
```

Each returned 20 semantic candidates. Filtering names and signatures for
`Solenoid`, `UniversalSolenoid`, or a rational `PontryaginDual` returned an
empty list for all four. The returned candidates were generic Pontryagin-dual,
profinite-category, and p-adic infrastructure, not an exact result.

The public grep.app code-index queries
`UniversalSolenoid`, `PontryaginDual Rat`, `ProfiniteIntegers`, and
`S-adic solenoid` all returned HTTP `503`. This is a named capability failure,
not negative search evidence. GitHub's code-search API query
`UniversalSolenoid language:Lean` returned HTTP `401 Requires authentication`,
and `gh auth status` confirmed that no GitHub host is authenticated. GitHub
repository-search queries found no solenoid or p-adic-solenoid Lean repository;
the sole `Pontryagin Lean` result was `willcforte/pontryagin-lean`, whose stated
subject is Pontryagin's Maximum Principle and is unrelated.

Accordingly the third-party code search is not claimed complete. Under the
repository rule this capability gap independently requires an `open` outcome;
it cannot be converted into a claim that no third-party implementation exists.

## Rejected approaches and fabrication boundary

- **Use the all-prime exact sequence for arbitrary `S`:** rejected. An instance
  at `S = P` does not prove a theorem quantified over all prime sets.
- **Treat all positive moduli as an arbitrary prime register:** rejected. The
  `CongruenceData` index and compatibility relation are fixed globally and
  expose no `S` parameter or specialization theorem.
- **Read `Character Sigma ≃+ Q` as `Sigma ≃ PontryaginDual Q`:** rejected. The
  former is `Sigma-hat ≃ Q`; the latter is the opposite dual direction. GICT
  theorem 6.6 explicitly fixes `Q-hat = Hom(Q,T)`.
- **Invoke abstract Pontryagin biduality:** rejected. No pinned theorem supplies
  the needed rational specialization or a checked evaluation equivalence for
  this carrier, and a nonconstructive slogan is not an addressable Lean edge.
- **Treat `hiddenKernelAddEquiv` as a topological equivalence:** rejected. The
  `≃+` structure proves additive equivalence, but carries no continuity or
  homeomorphism fields. No separate theorem supplies those missing properties.
- **Bind only the all-prime clause:** rejected. The atom is one coupled theorem;
  partial coverage would leave the arbitrary-`S` exact sequence unresolved.
- **Add a theorem to one of the existing carrier modules:** prohibited because
  every relevant module has an active freeze event.
- **Define `Sigma_S` so the exact sequence is true by construction:** rejected
  as hollow. A self-earning definition would install the desired kernel and
  projection instead of proving the source mathematics.

The minimum honest unlock is a new, unfrozen module with an independently
meaningful arbitrary-prime-set solenoid construction, structured injection and
projection maps, a uniform short-exactness theorem, an all-prime specialization,
an explicit topological additive equivalence with `PontryaginDual Q`, and a
topological/homeomorphic upgrade of the existing all-prime additive kernel
equivalence. Any exact third-party hit must be reused instead of reproved.

## Fidelity and non-hollowness accounting

- **Conclusion substance:** the source conclusions are nontrivial. No faithful
  complete Lean conclusion was produced because its carriers and bridge
  equivalences are absent.
- **Hypothesis satisfiability:** not reached for a candidate declaration. There
  is no source-faithful arbitrary-`S` signature to instantiate without first
  constructing the missing carrier.
- **Domain inhabitance:** the existing `UniversalSolenoid`, circle, rational,
  and p-adic domains are inhabited in checked modules. No term inhabiting a
  repository-defined `Sigma_S` can be exhibited because that type is absent.
- **Proof substance:** the five frozen component modules are substantive and
  compile, but conjoining them cannot manufacture the missing generality,
  reverse the dual direction, or add continuity to the kernel equivalence.
- **Duplicate search:** current-tree, pinned-mathlib, all-ref, Loogle, and
  LeanSearch traces are recorded above. Public code-index capability failures
  are explicitly named rather than hidden.
- **Clause fidelity:** every available partial bind has a nonempty
  dropped/weakened set. Deposit is blocked.
- **Rendered-statement fidelity:** not run because no Lean/Scribe candidate was
  created; there is no emitted statement to compare.

No unavailable obligation is passed as `ASSUMED-UNVERIFIED`. The unreachable
items are explicitly unresolved and force `open`.

## Grader-trap checklist

- **Instance vs general:** `S = P` cannot replace arbitrary `S`.
- **All moduli vs selected primes:** congruence coordinates over every positive
  modulus are not a parameterized prime-set product without a proved bridge.
- **Object vs dual:** `Sigma-hat ≃ Q` is not `Sigma ≃ Q-hat`.
- **Additive vs topological equivalence:** `hiddenKernelAddEquiv` settles the
  additive structure, but `≃+` alone does not prove continuity or a
  homeomorphism.
- **Element-level vs topological exactness:** the current exact sequence claims
  only element-level `Function.Exact`; no topology is packaged into the maps.
- **Proof-internal vs addressable:** commentary about standard duality does not
  supply a declaration GID.
- **Multi-clause residue:** arbitrary-`S` exactness, all-prime specialization,
  rational duality, and kernel structure are separately accounted for.
- **Residual record vs coverage:** the selected GICT atom has a canonical
  residual-open backfill record whose coverage and Scribe receipt lists are
  empty. The three PZG receipts and separate Observer receipt concern different
  atoms; none covers this GICT atom.

## Commands not run

- `make deposit`: not run because clause fidelity and third-party search
  completeness fail.
- `make preflight`: not run because there is no deposit candidate.
- `make cover`: not run because deposit/preflight were not reached and partial
  coverage would be dishonest.
- `make lean`: not run; this report changes no Lean source. The proportionate
  scoped carrier build is recorded below.
- `make emit`: not run because no Scribe source or projection changed.
- `git push` and `make pr-open`: not run by dispatcher instruction.

## Verification

The historical scoped build after the first synchronization to `901b052a` was:

```sh
lake build \
  D5.S1.Solenoid.ExactSequence \
  D5.S3.Factorization.SolenoidProfiniteKernel \
  D5.S1.Dynamics.SolenoidCharacter
```

Exit `0`; Lean reported `Build completed successfully (8563 jobs)`.

After the final merge to content base `9014d610`, the refreshed scoped build
included the modules defining and constructing the additive kernel equivalence:

```sh
lake build \
  D5.S1.Solenoid.ExactSequence \
  D5.S3.Factorization.SolenoidProfiniteKernel \
  D5.S3.Observer.StreamlineTheorem \
  D5.S3.Observer.HiddenFlow.StreamlineExistence \
  D5.S1.Dynamics.SolenoidCharacter
```

Exit `0`; Lean reported `Build completed successfully (8567 jobs)`. It replayed
one pre-existing `longLine` style warning from
`D5/S3/Arith/HiddenFiberRigidity.lean`; no source in this report-only change was
compiled with an error. `make dotnet` also exited `0` with zero warnings and
zero errors.

The final `digest-status --json` query on the refreshed Lean report again
returned `alignment=seen`, `migration=residual`, `truth=open`,
`deletable=false`, and only `coverage-gid-missing` for the selected atom.

The latest actual deposit template on this final base was inspected with:

```sh
git log --no-merges -20 --format='%H %s' --grep='^formalize: deposit'
git show 4813e833027e17f30e7b1c4c5144d87514114086
```

It is the incoming `SearchableWindowDecision` deposit and adds one new Lean
module, one Scribe source, and one emitted Blueprint Markdown file; its
separate receipt/freeze commit is
`0f9cfb7351a0a961340722926b2bfbdcf2707f2d`.
No candidate artifacts were created because the task stopped at the
fidelity/search gate.
