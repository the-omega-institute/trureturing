# A397434 implementation record

Outcome: **成**. The repository module
`D5/S3/ArithSums/A397434ThresholdAnf.lean` proves the adjacent-equality
classification for the count sequence defined by `reducedCoeffBit` and is
frozen by the accepted Freeze event
`sha256:5b40f852d9e58ad2cd64542347dcd43032c31e47d0c11b0487348fd6be80068b`.
This correction pass changes reporting and provenance text only; it does not
change proof terms or frozen theorem statements.

## Source statement and exact theorem

The authoritative input was `make show-atom
ATOM_ID=78808693fcf6b5b99e219f6a4387acec4c87f79e8b0b5a9bfc94f8ea0c2be37a`
(exit 0). It identifies source `pzg-v170`,
`docs/develop/theory/PZG_BEDC.md`, and the matching raw, normalized, and CAS
hash `sha256:78808693fcf6b5b99e219f6a4387acec4c87f79e8b0b5a9bfc94f8ea0c2be37a`.
The atom's requested cover is the zero-assumption main result:

```text
forall n : Nat, 1 <= n ->
  (a n = a (n + 1) <-> n % 4 = 2)
```

Lean's exact declaration is
`D5.S3.ArithSums.A397434ThresholdAnf.a_eq_succ_iff_mod_four`, with statement
id `sha256:adac79fb9c9d22a6fecc56192d53654c68bd8cc8b74daec054df5f23390cef49`.
The hypothesis `1 <= n` is exactly the atom's stated `n >= 1` boundary; the
coverage edge therefore has no residual hypothesis.

## Correction ledger (verbatim)

### (i) Condition (iv) evidence

Before:

```text
the atom coverage edge points directly to this declaration
```

After:

```text
the live proof path is `a_eq_succ_iff_mod_four -> even_step_eq_iff -> even_step_eq_of_odd -> anf_count_even_bridge, S_empty_of_odd; even_step_strict_of_even -> mem_S_of_even, anf_count_even_bridge; odd_step_strict -> shifted_row_pos`. The positive-even branch takes `d = m + 1`; the odd branch covers `m = 0`, hence `n = 1`. The atom coverage edge is bookkeeping, not proof-consumption evidence.
```

The replacement is the source-derived proof path; coverage is recorded only as
an accounting edge.

### (ii) Semantic boundary

Before (the Scribe paragraph): `For n variables, take the Boolean function that
is one when at least ceil(n/2) variables are one. Its algebraic normal form over
GF(2) has one squarefree monomial for each supported subset, and a(n) is the
cardinality of this support.`

Before (the Lean `digest` line):

```text
digest: Adjacent threshold ANF support counts agree exactly at indices two modulo four. -/
```

After (the Lean header and Scribe): `The Lean module defines a(n) from
reducedCoeffBit, and thresholdAnfSupport filters that same reduced bit. It
proves the adjacent classification for this reduced-coefficient count
sequence. The intended identification with the OEIS ANF support counts uses
Meaux's ANF coefficient reduction, stated separately below, but the main proof
does not consume that declaration; the Boolean-function -> Mobius-coefficients
-> reduced-bit -> support-count semantic bridge is therefore not machine-closed
in this module.`

The corresponding current Lean `digest` is:

```text
digest: Proves the adjacent classification for the count sequence defined by reducedCoeffBit; thresholdAnfSupport filters that same reduced bit. The semantic identification with OEIS ANF support counts relies on Meaux's ANF coefficient reduction, stated separately as threshold_anf_coefficient_reduction, but that declaration is not consumed by the main proof, so the Boolean-function -> Mobius-coefficients -> reduced-bit -> support-count bridge is not machine-closed here. -/
```

This delivery selects option (a): the identification bridge is stated as an
explicit open boundary because `threshold_anf_coefficient_reduction` is not
consumed by the main proof. Option (b) was not attempted; no theorem or proof
term was changed to manufacture that consumption.

### (iii) OEIS formula

Before (report):

```text
The OEIS entry also proves `a(2k+1) = 2^(2k) - 1`, but it gives no proof or counterexample for the adjacent-equality conjecture itself.
```

Before (OEIS card):

```text
the separate special-index identity `a(2k+1) = 2^(2k)-1`
```

After, quoted verbatim from the OEIS `%F` line: `a(2^k+1) = 2^(2^k) - 1 for k
>= 1.`

The already-merged `docs/develop/theory/PZG_BEDC.md` atom text retains its
separate typo for the follow-up annotation requested by the ruling; it is not
part of this lane's edit.

Formula-location answer: yes, this lane contained the mistaken formula in the
OEIS library card and the implementation report; it did not occur in the Lean
header or Scribe source. The merged dev atom occurrence is outside this lane.

### (iv) Literature cards

Before (`meaux2019threshold.md` body):

```text
Carlet and Meaux restate the result as Lemma 2 in their later study of direct sums of monomials and threshold functions. The source record cites this as Meaux (2021), Lemma 2, and records its attribution to Meaux (2019), Theorem 1.
```

Before (`carlet2022threshold.md` claim):

```text
Lemma 2 states the algebraic-normal-form coefficient reduction for threshold functions and attributes it to Meaux's 2019 Theorem 1.
```

Before (`carlet2022threshold.md` body):

```text
The source record uses the 2021 citation year. Crossref identifies the work by DOI `10.1109/TIT.2021.3139804`; its metadata records DOI creation in 2021 and journal publication in volume 68, issue 5, in 2022.
```

After (card claims and provenance pointer):

```text
The 2019 ePrint is the source cited as [Méa19], Theorem 1; the exact theorem body and coefficient formula remain ASSUMED-UNVERIFIED here.
Méaux's 2021 single-author paper labels Lemma 2 '([Méa19], Theorem 1)' for the threshold-function ANF coefficient reduction; the exact lemma body remains ASSUMED-UNVERIFIED here.
This is a distinct Carlet--Méaux paper; its Lemma 2 content was not fully verified in this run and remains ASSUMED-UNVERIFIED.
FromLiterature(ThresholdAnf) -> D5/L/ArithSums/meaux2021threshold
```

The full text of the 2019 theorem, the full text of the 2021 Lemma 2, and the
Carlet--Méaux Lemma 2 were not independently obtained in this run; those
portions remain explicitly `ASSUMED-UNVERIFIED` in the cards.

## Formal semantic coverage boundary

This module proves the adjacent classification for the count sequence defined
directly by `reducedCoeffBit`; `thresholdAnfSupport` also filters that same
reduced bit. The semantic identification with the OEIS ANF support count uses
Méaux's ANF coefficient reduction, stated separately as
`threshold_anf_coefficient_reduction`, but the main proof does not consume that
declaration. Therefore the full semantic chain from the actual Boolean
function through Möbius coefficients, reduced bits, and support counting is not
machine-closed in this module. This delivery chooses option (a), an explicit
boundary statement, rather than option (b).

The module-level admission basis is `escape-witness`. The header records
`generality: G`, `mirror-B: D5/B/S3/ArithSums/A397434ThresholdAnf`,
`mirror-E: none(waiver:general-symbolic-proof-no-numeric-artifact)`,
`anchors: []`, and `utility: none` because this is a general symbolic
number-theoretic result, not a finite certificate, checker, or numerical
reduction.

## Declaration audit

The raw Lean report records 39 declarations in the frozen statement set: 8
definitions, 10 public theorems, and 21 private support declarations. The
public surface is audited below. `FromLiterature` means the theorem is an
implementation of the cited result and receives no escape-witness credit;
`FromRepo` means the theorem is derived in this module from the atom's route.
Definitions have no theorem admission basis.

| Declaration | Shape | Escape witness and four-part check | Admission basis | Provenance |
| --- | --- | --- | --- | --- |
| `thresholdAnfCoeff` | definition | none; carrier definition | not applicable | FromRepo |
| `reducedCoeffBit` | definition | none; coefficient-bit definition | not applicable | FromRepo |
| `thresholdAnfSupport` | definition | none; filtered powerset definition | not applicable | FromRepo |
| `thresholdMonomialCount` | definition | none; degree-grouped count definition | not applicable | FromRepo |
| `a` | definition | none; A397434 count definition | not applicable | FromRepo |
| `pBit` | definition | none; adjacent-row parity definition | not applicable | FromRepo |
| `rowSumZ` | definition | none; integer row-sum definition | not applicable | FromRepo |
| `S` | definition | none; adjacent-binomial support-set definition | not applicable | FromRepo |
| `threshold_anf_coefficient_reduction` | content | none for admission: local proof of the cited Meaux formula; deliberately excluded from escape accounting | not applicable to escape accounting | FromLiterature: Méaux (2021), Lemma 2, attributed to Méaux (2019), Theorem 1 |
| `threshold_support_card` | bind-only | none; `Finset.sum_powerset_apply_card` plus normalization | not applicable as an independent freeze basis | FromRepo/Mathlib binding |
| `a_eq_threshold_support_card` | bind-only | none; projection of `threshold_support_card` | not applicable as an independent freeze basis | FromRepo binding |
| `anf_count_even_bridge` | content | preregistered witness 2, the exact integer adjacent-row difference. (i) Inspector closure contains the local row bridge path; (ii) it is not obtained by frozen-theorem instantiation; (iii) it is a new integer identity over `S m`; (iv) `even_step_eq_of_odd` and `even_step_strict_of_even` consume it on the live path | escape-witness | FromRepo |
| `S_empty_of_odd` | content | preregistered witness 1, odd half of the `S m` parity split. (i) Inspector closure contains the local Lucas/parity path; (ii) it is not a frozen projection; (iii) set emptiness is not a restatement of the final residue theorem; (iv) `even_step_eq_of_odd` consumes it | escape-witness | FromRepo |
| `mem_S_of_even` | content | preregistered witness 1, even half of the `S m` parity split. (i) Inspector closure contains its local construction; (ii) it is not a frozen projection; (iii) membership of `m + 1` is a distinct intermediate fact; (iv) `even_step_strict_of_even` consumes it | escape-witness | FromRepo |
| `endpoint_not_mem_S` | bind-only | none; endpoint exclusion is a direct application of Mathlib `Nat.two_dvd_centralBinom_of_one_le` with local normalization | not applicable as an independent freeze basis | FromRepo/Mathlib binding |
| `odd_step_strict` | content | the positive shifted-row calculation used by the odd-row step. (i) Inspector closure contains `shifted_row_pos`; (ii) positivity is not a frozen projection; (iii) strict positivity of the added row is distinct from the equality classification; (iv) `odd_step_strict` consumes it directly | escape-witness (module credit is supplied by the preregistered `S m` witnesses) | FromRepo |
| `even_step_eq_iff` | content | the even-index classification assembled from the exact bridge and the two parity halves. (i) Inspector closure contains `anf_count_even_bridge`, `S_empty_of_odd`, and `even_step_strict_of_even`; (ii) the iff is not a frozen projection; (iii) it classifies `2*m` by `Odd m`; (iv) the main residue theorem consumes it | escape-witness (inherits the live `S m` witness path) | FromRepo |
| `a_eq_succ_iff_mod_four` | content | the public residue classification. (i) Inspector closure contains the odd/even case split and both strict/equality branches; (ii) no frozen theorem has this conclusion; (iii) it is the atom's global iff, not an alias of a prerequisite; (iv) the live proof path is `a_eq_succ_iff_mod_four -> even_step_eq_iff -> even_step_eq_of_odd -> anf_count_even_bridge, S_empty_of_odd; even_step_strict_of_even -> mem_S_of_even, anf_count_even_bridge; odd_step_strict -> shifted_row_pos`. The positive-even branch takes `d = m + 1`; the odd branch covers `m = 0`, hence `n = 1`. The atom coverage edge is bookkeeping, not proof-consumption evidence. | escape-witness (live paths from witnesses 1 and 2) | FromRepo |

The four criteria above were checked against the elaborated kernel dependency
closure, not source-text search. The inspector invocation was
`tools/lean-inspector/Inspector.lean --dependencies`; it emitted the module
manifest and 73-line `dependencies.ndjson` in the runner attempt directory.
The closure contains the local declarations named in the table and the
Mathlib constants used by their proofs. No private upstream D5 declaration is
treated as a frozen prerequisite.

Every declaration has `direct_frozen_dependencies: []`: the module imports only
`Init` and pinned `Mathlib`, and no earlier D5 module is imported. The local
private declarations listed in the active-edge paragraph are proof dependencies,
not baseline frozen nodes.

The two named bind-only companions have live consumer edges in this delivery:

| Consumer | Prerequisite | Kernel/source evidence |
| --- | --- | --- |
| `a_eq_threshold_support_card` | `threshold_support_card` | theorem body is exactly `(threshold_support_card n ((n + 1) / 2)).symm` |
| private `a_odd_row` | `a_eq_threshold_support_card` | `rw [a_eq_threshold_support_card, threshold_support_card, thresholdMonomialCount_cast]` |
| private `a_even_row` | `a_eq_threshold_support_card` | `rw [a_eq_threshold_support_card, threshold_support_card, thresholdMonomialCount_cast]` |

The companion theorem is therefore consumed by named proofs in the same
delivery; it is not an independent module or deposit rationale. The supporting
active edges include `anf_count_even_bridge -> row_bridge`,
`row_bridge -> rowSumZ_succ, weighted_product_sum_eq_S, pBit_pascal`,
`weighted_product_sum_eq_S -> product_eq_indicator_S`,
`even_step_eq_iff -> even_step_eq_of_odd, even_step_strict_of_even`, and the
main live path is
`a_eq_succ_iff_mod_four -> even_step_eq_iff -> even_step_eq_of_odd ->
anf_count_even_bridge, S_empty_of_odd`,
`even_step_strict_of_even -> mem_S_of_even, anf_count_even_bridge`, and
`a_eq_succ_iff_mod_four -> odd_step_strict -> shifted_row_pos`.
The coverage edge is an accounting edge only; it is not evidence of proof
consumption.

## ANF reduction search and provenance

The required rerun searched the repository D5 declarations and the pinned
Mathlib revision (`db584cd6d46c92f209a44c0f1c829460d327499d`) for the threshold
ANF coefficient statement. Both exact searches returned no hit (exit 1).
LeanSearch was queried for the threshold Boolean ANF coefficient and for the
Lucas parity characterization. It returned only generic Boolean-ring/binomial
items and the Mathlib Lucas family, not the target theorem. The usable local
Mathlib identities are applied directly where appropriate, including
`Choose.choose_modEq_choose_mod_mul_choose_div_nat`; the threshold coefficient
formula itself remains a local implementation of the separate Méaux (2021)
single-author paper's Lemma 2, attributed there to Méaux (2019), Theorem 1;
the exact 2021 lemma body remains `ASSUMED-UNVERIFIED` in the literature card.

The wider source checks recorded HTTP 401 for GitHub code search and HTTP 429
for the rerun of grep.app (the probe recorded HTTP 503 twice). These indexes do
not establish exhaustive third-party coverage, so absence outside the opened
sources is `ASSUMED-UNVERIFIED`. No priority claim is made. The sequence is
attributed to OEIS A397434 and Tanguy Gautier Loïc Le Mer (2026); the proof
provenance for the adjacent-equality theorem is `FromRepo`. Its `%F` line is
quoted exactly as `a(2^k+1) = 2^(2^k) - 1 for k >= 1.`; it gives no proof or
counterexample for the adjacent-equality conjecture itself.

## Probe-to-module delta

The 368-line probe was byte-compared with the final module. The formal module
adds the required D5 header and changes namespace `A397434Probe` to
`D5.S3.ArithSums.A397434ThresholdAnf`. It removes probe-only `#print axioms`
commands. The coefficient theorem's comment is shortened to mathematical
provenance, and comments for the two `S m` halves and the bridge are changed to
reader-facing statements. Two private row proofs now route through the named
support-card companion, and the positive-even proof explicitly excludes the
`d = 2m` endpoint before proving a strict interior bound. The final source is
371 lines. No proof term was weakened and no `native_decide`, `sorry`, or extra
axiom was introduced.

## Sizes, frozen identities, and axioms

Before this change, `D5/S3/ArithSums` contained 5 Lean files and its Scribe
source bucket contained 5 `.scribe.cs` files. After the addition both contain
6 files, below the live `DirectoryFileLimit = 48`. The generated Blueprint
oracle is 42 lines; the Scribe source is 107 lines; the Lean source is 371
lines. The frozen module statement id is
`sha256:80beeea9473566649a3f42be9c7925ef17855f04c8746b6f85cd2d33699e45b0`.

The raw report gives the public statement ids for the main theorem and the
two bind-only companions as follows:

```text
threshold_support_card       sha256:4233989195840661aacde95c6f5b81abf716b86b6f57c247668013218f97a14b
a_eq_threshold_support_card  sha256:3858b3b6cb7ed46df236b2673e49bdf72a591c4199335367d9907b8750c0d565
a_eq_succ_iff_mod_four       sha256:adac79fb9c9d22a6fecc56192d53654c68bd8cc8b74daec054df5f23390cef49
```

All public theorem closures and the module's definitions use only
`{propext, Classical.choice, Quot.sound}`. The dependency manifest contains
no `sorryAx`; no `native_decide` occurs in the source or closure.

The SL-033 frozen-pair accounting is exactly two changed halves: one accepted
Freeze event and one matching frozen state file. The accepted event records
`declaration_statement_ids` for the 39-member module statement set; the state
file records the same module statement id. The atom coverage file is separate
digestion state and does not replace either half.

## Gate ledger (UTC)

All commands were run with `LC_ALL=C LANG=C` where locale-sensitive. Exit codes
are the command exit codes, not pipeline statuses.

| Gate | Command | UTC window | Exit |
| --- | --- | --- | ---: |
| build | `LC_ALL=C LANG=C make lean` | 02:48:03Z-02:48:32Z | 0 |
| report | `LC_ALL=C LANG=C make lean-report` | 02:48:36Z-02:48:55Z | 0 |
| emit (first pass) | `LC_ALL=C LANG=C make emit` | 02:48:59Z-02:49:59Z | 0 |
| emit (idempotence pass) | `LC_ALL=C LANG=C make emit` | 02:50:04Z-02:51:02Z | 0 |
| Scribe content | `LC_ALL=C LANG=C STRATALINT_SCRIBE_BASE=b1c1c8b07e35963ab2a347bd100550cf3b425884 bash tools/scripts/workflow/scribe-content-checks.sh .lake/build/stratalint/raw-lean-report.json` | 02:51:12Z-02:51:46Z | 0 |
| C# documents build | `LC_ALL=C LANG=C dotnet build tools/StrataLint.Scribe.Documents/StrataLint.Scribe.Documents.csproj --configuration Release --no-restore` | 02:51:51Z-02:52:06Z | 0 |
| original deposit/freeze (historical) | `make deposit BASE=a9e459eef9464bc0d2443f65d4669c4ef2aa3830 ATOM_ID=78808693fcf6b5b99e219f6a4387acec4c87f79e8b0b5a9bfc94f8ea0c2be37a GID=D5/S3/ArithSums/A397434ThresholdAnf.a_eq_succ_iff_mod_four` | 01:36:39Z-01:40:06Z | 0 |
| correction-pass deposit/cover | not run: all statement IDs were unchanged | N/A | N/A |

The final Scribe checks reported `DESCRIBE_STATUS ... red=0` and
`markdown: judged=1 formula(s)=2 red=0`. The canonical report delta was
`changed=0 added=9 removed=0 recheck=9`, with raw report SHA-256
`cc4ef1998447357f66dd1d61a477bebfa790421589016ea4a8c6a474725bd41b`.
The historical deposit ledger reported `added=1 changed=0 conflicts=0`; its
Freeze event hash is the one named at the top of this report.

Statement-id accounting for this correction pass is unchanged before/after:

| Declaration | Before | After | Deposit/cover |
| --- | --- | --- | --- |
| `threshold_support_card` | `sha256:4233989195840661aacde95c6f5b81abf716b86b6f57c247668013218f97a14b` | same | not repeated |
| `a_eq_threshold_support_card` | `sha256:3858b3b6cb7ed46df236b2673e49bdf72a591c4199335367d9907b8750c0d565` | same | not repeated |
| `a_eq_succ_iff_mod_four` | `sha256:adac79fb9c9d22a6fecc56192d53654c68bd8cc8b74daec054df5f23390cef49` | same | not repeated |

## Atom terminal state

The atom file moved from
`Meta/Digestion/backfill/pzg-v170/residual-open/78808693fcf6b5b99e219f6a4387acec4c87f79e8b0b5a9bfc94f8ea0c2be37a.yaml`
to
`Meta/Digestion/backfill/pzg-v170/absorbed-closed/78808693fcf6b5b99e219f6a4387acec4c87f79e8b0b5a9bfc94f8ea0c2be37a.yaml`.
Its sole coverage edge is
`D5/S3/ArithSums/A397434ThresholdAnf.a_eq_succ_iff_mod_four` with the exact
statement id above, and `unresolved_subitems: []`. The terminal atom state is
`absorbed-closed`.
