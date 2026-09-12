# A397434 implementation record

Outcome: **成**. The repository module
`D5/S3/ArithSums/A397434ThresholdAnf.lean` proves the atom's unconditional
adjacent-equality classification and is frozen by the accepted Freeze event
`sha256:5b40f852d9e58ad2cd64542347dcd43032c31e47d0c11b0487348fd6be80068b`.
No push or pull request was made.

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
| `a_eq_succ_iff_mod_four` | content | the public residue classification. (i) Inspector closure contains the odd/even case split and both strict/equality branches; (ii) no frozen theorem has this conclusion; (iii) it is the atom's global iff, not an alias of a prerequisite; (iv) the atom coverage edge points directly to this declaration | escape-witness (live paths from witnesses 1 and 2) | FromRepo |

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
`even_step_eq_iff -> even_step_eq_of_odd, even_step_strict_of_even`, and
`a_eq_succ_iff_mod_four -> even_step_eq_iff, odd_step_strict`.

## ANF reduction search and provenance

The required rerun searched the repository D5 declarations and the pinned
Mathlib revision (`db584cd6d46c92f209a44c0f1c829460d327499d`) for the threshold
ANF coefficient statement. Both exact searches returned no hit (exit 1).
LeanSearch was queried for the threshold Boolean ANF coefficient and for the
Lucas parity characterization. It returned only generic Boolean-ring/binomial
items and the Mathlib Lucas family, not the target theorem. The usable local
Mathlib identities are applied directly where appropriate, including
`Choose.choose_modEq_choose_mod_mul_choose_div_nat`; the threshold coefficient
formula itself remains a local implementation of Méaux (2021) Lemma 2 / Méaux
(2019) Theorem 1.

The wider source checks recorded HTTP 401 for GitHub code search and HTTP 429
for the rerun of grep.app (the probe recorded HTTP 503 twice). These indexes do
not establish exhaustive third-party coverage, so absence outside the opened
sources is `ASSUMED-UNVERIFIED`. No priority claim is made. The sequence is
attributed to OEIS A397434 and Tanguy Gautier Loïc Le Mer (2026); the proof
provenance for the adjacent-equality theorem is `FromRepo`. The OEIS entry
also proves `a(2k+1) = 2^(2k) - 1`, but it gives no proof or counterexample for
the adjacent-equality conjecture itself.

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
oracle is 42 lines; the Scribe source is 101 lines; the Lean source is 371
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
| build | `make lean` | 01:28:01Z-01:28:18Z | 0 |
| report | `make lean-report` | 01:28:26Z-01:30:28Z | 0 |
| emit | `make emit` | 01:31:40Z-01:32:34Z | 0 |
| Scribe content | `bash tools/scripts/workflow/scribe-content-checks.sh ...` | 01:35:57Z-01:36:23Z | 0 |
| C# documents build | `LC_ALL=C LANG=C dotnet build tools/StrataLint.Scribe.Documents/StrataLint.Scribe.Documents.csproj --configuration Release --no-restore` | 01:48:51Z-01:48:53Z | 0 |
| deposit/freeze | `make deposit BASE=a9e459eef9464bc0d2443f65d4669c4ef2aa3830 ATOM_ID=78808693fcf6b5b99e219f6a4387acec4c87f79e8b0b5a9bfc94f8ea0c2be37a GID=D5/S3/ArithSums/A397434ThresholdAnf.a_eq_succ_iff_mod_four` | 01:36:39Z-01:40:06Z | 0 |

The final Scribe checks reported `DESCRIBE_STATUS ... red=0` and
`markdown: judged=8 formula(s)=14 red=0`. The canonical report delta was
`changed=0 added=9 removed=0 recheck=9`, with raw report SHA-256
`fc4fb98ba19494f7081339a1da629ec51f638caec716bae7b9e957601984a0cd`.
The deposit ledger reported `added=1 changed=0 conflicts=0`; its Freeze event
hash is the one named at the top of this report.

## Atom terminal state

The atom file moved from
`Meta/Digestion/backfill/pzg-v170/residual-open/78808693fcf6b5b99e219f6a4387acec4c87f79e8b0b5a9bfc94f8ea0c2be37a.yaml`
to
`Meta/Digestion/backfill/pzg-v170/absorbed-closed/78808693fcf6b5b99e219f6a4387acec4c87f79e8b0b5a9bfc94f8ea0c2be37a.yaml`.
Its sole coverage edge is
`D5/S3/ArithSums/A397434ThresholdAnf.a_eq_succ_iff_mod_four` with the exact
statement id above, and `unresolved_subitems: []`. The terminal atom state is
`absorbed-closed`.
