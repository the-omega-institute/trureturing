# Matching Monomial Fiber Cardinality

skill: consensus-rnd:sshx
producer: one codex-cli implementation worker
independent_review: ASSUMED-UNVERIFIED (zero review seats)

Repository: https://github.com/the-omega-institute/trureturing
Branch: lane/math/matching-equiv-0908
Base: ceb8502be9e6ccabf98518284f0051b971e7104b
Lane: #6377. Predecessor: #6433.

All five requested steps are proved and pushed. The exact main theorem is
`MatchingEquiv.card_matchingMonomialFiber`; the endpoint is
`MatchingPolynomial.matching_identity : MatchingIdentity`.
There is no remaining Lean goal for this brief.

The user brief preregisters the fiber equivalence as the proposed escape
witness. The orchestrator checked only the numerical readings listed in
that brief. All Lean results in this report are worker-run.

## Bind-only Probe

The pure cardinality target was tested again, independently of the previous
MatchingIdentity probe. The attempt rewrites the first factor with
card_partner_embeddings, specializes Fintype.card_embedding_eq, normalizes
finite-set cardinalities, and calls linarith only with that equality and
sq_nonneg of the rational cast of the fiber cardinality.

`/usr/bin/time -l make lean`: EXIT 2; 12591 jobs; 41.68 seconds;
maximum resident set size 5935546368 bytes. The cache receipt says both
project and Mathlib oleans are warm. The failure is at MatchingFiber.lean:597:

```text
linarith failed to find a contradiction
hEmbedding : Fintype.card (S ↪ (S ∪ T)ᶜ) =
  (n - (S.card + T.card)).descFactorial S.card
a : Fintype.card (MatchingMonomialFiber k S T) <
  Fintype.card (S ↪ (S ∪ T)ᶜ) *
    ((2 * (k - S.card)).factorial / ((k - S.card).factorial * 2 ^ (k - S.card)))
⊢ False
```

The exact source and raw log are bind-only-attempt.lean and
bind-only-make-lean.log in the attempt directory. The temporary example was
removed. This is a failed restricted attempt, not a semantic nonexistence claim.

## Search Decision

Pinned Mathlib provides Equiv.Perm.card_of_cycleType_mul_eq and
Equiv.Perm.card_of_cycleType. The type consisting of h transpositions is
Multiset.replicate h 2. We directly specialize that formula; no independent
proof of the perfect-matching recurrence and no third-party port is needed.

An earlier name search found TauCeti.card_perfectMatching at revision
f6f910c48c3b832f64090230c1d623c1a98a9b58, with Apache-2.0 LICENSE and no NOTICE
in its recursive Git tree. Its Lean v4.34.0-rc2 and Mathlib
e21ec05048292b3de86d4cf1987e2208171a5642 differ from this repository. A port
was considered, then superseded before implementation by the pinned-Mathlib
cycle-type hit. No TauCeti code is copied into the delivered source.

The primary count uses a multiplication equality in N. The denominator
h.factorial * 2^h is positive, so the natural-number quotient follows by
exact division. This also handles h=0 without a negative double factorial.

## Not Claimed

No H_0(R) positive semidefiniteness, complete parity identity, or all-order
omission of H_1 is asserted. Freeze, coverage, and independent review are
not claimed by local Lean compilation.

## Step 1

The two count theorems compile with `/usr/bin/time -l make lean`: EXIT 0;
12592 jobs; 25.53 seconds; maximum RSS 1746518016 bytes
(step-1d-make-lean.log). Both public theorem axiom prints and the private
cycle-type characterization print are [propext, Classical.choice, Quot.sound].

Both public theorems have proof_shape bind-only and no direct frozen
repository premises (GID/statement_id: none). Their admission_basis is
rule-11-upstream-wrapper, for the preregistered consumer
card_matchingMonomialFiber -> card_fixedPointFreeInvolution. The product
count directly specializes Equiv.Perm.card_of_cycleType_mul_eq; the quotient
count consumes the product count. escape_witness: none for both.

utility is none separately for FixedPointFreeInvolution, its finite instance,
the private involution_iff_cycleType, card_fixedPointFreeInvolution_mul, and
card_fixedPointFreeInvolution: each is a symbolic type, type-class instance,
or universally quantified theorem at arbitrary finite cardinality. None
enumerates bounded parameters, certifies a numerical instance, implements
a checker, or reduces a theorem to undischarged numerical premises.

Earlier step-1 builds failed on local API/normalization details:
step-1a EXIT 2 / 17.88 s / RSS 3054321664; step-1b EXIT 2 / 14.13 s /
RSS 1729609728; step-1c EXIT 2 / 13.12 s / RSS 1728692224. All report 12592
jobs. Errors concerned the explicit finite instance, cancellation of two,
Finset.eq_univ_of_card's explicit finset, the argument order of exact
division, and a List-only lemma name. No resource limit was raised.

Step 1 was pushed as `5b2086e96f`.

## Step 2

The exact requested `card_matchingMonomialFiber` is proved, together with
`card_matchingMonomialFiber_mul`. The explicit equivalence reconstructs the
square and cross edges, proves they are loop-free and pairwise disjoint,
counts their union, and assigns the unique local choice selected by S.
Disjoint edge supports give the required exponent sum and injectivity of
the decoration exponent. Both extracted partner maps are recovered by
uniqueness of the edge incident to a given vertex.

The equivalence needs hST, hS and hT; the requested hk hypothesis is retained
in the quotient theorem's signature, although it is unnecessary for counting
the possibly empty embedding type. No parameter restriction was weakened in
the requested theorem. The product form is the coefficient-field consumer's
interface, avoiding any cast of natural-number division.

`/usr/bin/time -l make lean`: EXIT 0; 12593 jobs; 22.04 seconds;
maximum RSS 3019046912 bytes (`step-2h-make-lean.log`). Every added theorem's
`#print axioms` has [propext, Classical.choice, Quot.sound]. The earlier
step-2c through step-2g failures concern dependent choice normalization,
explicit incidence vertices, and local API arguments; no bound was raised.

The constructive public results have proof_shape content after inlining
their live local construction; no direct frozen repository theorem is used
(GID/statement_id: none). The two normalization companions
matching_edge_eq_of_mem and decorationExponent_injective are conservatively
classified bind-only, with no independent deposit basis. The proposed and
observed escape is the brief's square-partner/cross-involution decomposition;
the companion consumer is fiberToFactors_injective. The constructive
results use admission_basis escape-witness and matchingMonomialFiberEquiv
is consumed by both cardinality theorems. The final audit below gives each
declaration separately.

Every added definition, instance, private helper and public theorem has
utility none: it describes or proves a symbolic construction for arbitrary
n,k,S,T; it neither enumerates bounded parameters, certifies a numerical
instance, implements a checker, nor leaves a numerical reduction obligation.

Step 2 was pushed as `d7a78b89fe`.

## Step 3

`coeff_matchingSum_fiber` proves (C) over Q for all parameters in the brief.
Its denominator is the rational product `(n-2k)! * (k-|S|)!`; its numerator
is `(-1)^(k-|S|) * (n-2k+|S|)! * (2*(k-|S|))!`. This is the stated pair
of factorial ratios, combined into one field quotient. The proof casts the
division-free count, uses Nat.factorial_mul_descFactorial, and cancels
the powers of two. There is no natural-number quotient cast.

`/usr/bin/time -l make lean`: EXIT 0; 12593 jobs; 23.38 seconds;
maximum RSS 3035693056 bytes (`step-3a-make-lean.log`). Its `#print axioms`
is [propext, Classical.choice, Quot.sound]. proof_shape content, through
the live fiber equivalence; escape_witness matchingMonomialFiberEquiv;
admission_basis escape-witness; direct frozen GID/statement_id none.
utility none: this is an unbounded symbolic coefficient formula, missing
all four computational classes. Consumer edge: (star) ->
coeff_matchingSum_fiber -> card_matchingMonomialFiber_mul.

Step 3 was pushed as `cf625f5a04`.

## Step 4

`matchingSum_esymm_mul` and `matchingSum_esymm` prove (star) in the
multivariate polynomial ring over Q. The first uses a constant-polynomial
denominator on the left; the second multiplies the explicit
`matchingNumerator` by the constant polynomial of its rational reciprocal.

The arbitrary-exponent obligation is also discharged. Every decorated
matching exponent is at most two at each vertex and has sum 2k. The same
holds for every subset pair contributing to e_i e_(2k-i). Every such
exponent is reconstructed as a disjoint square/linear fiber; coefficients
outside this class vanish on both sides. The surviving sum is reindexed by
i = |S| + ell, and uses alternating_factorial_sum with
d = n-2k+|S| and h = k-|S|. No finite parameter testing is a premise.

`/usr/bin/time -l make lean`: EXIT 0; 12594 jobs; 19.58 seconds;
maximum RSS 3110420480 bytes (`step-4b-make-lean.log`). The preliminary
support proof build `step-4a-make-lean.log` also passed, 18.13 seconds,
RSS 2986377216 bytes, 12594 jobs. All 12 theorem axiom prints in the new
module are [propext, Classical.choice, Quot.sound].

Both public theorems have proof_shape content after live helper inlining,
escape_witness matchingMonomialFiberEquiv together with the exponent
classification and shifted sum assembly; admission_basis escape-witness.
Direct frozen GID/statement_id: none. utility none for each of the 14
declarations: each is a symbolic definition or an unbounded theorem,
outside the four computational classes. No freeze or independent review
is claimed.

Step 4 was pushed as `8637dd6e4f`.

## Step 5

`matching_identity : MatchingIdentity` is proved. Evaluation of (star) in R,
Mathlib's Multiset.prod_X_sub_C_coeff and
MvPolynomial.aeval_esymm_eq_multiset_esymm, followed by
symmetrize_coefficient, gives the all-degree identity. Descending factorials
are converted through Nat.factorial_mul_descFactorial; all factorial
denominators are proved nonzero. The final proof normalizes multiplication
inside the finite sum before applying the evaluated identity.

`/usr/bin/time -l make lean`: EXIT 0; 12594 jobs; 17.46 seconds;
maximum RSS 3137781760 bytes (`step-5c-make-lean.log`). The 18 theorem axiom
prints in MatchingPolynomial are [propext, Classical.choice, Quot.sound].
The first attempt failed because the local namespace parsed R[X] as an
index expression (step-5a: EXIT 2, 25.37 s, RSS 3081879552). The second
failed because linarith treated differently parenthesized sum terms as
different atoms (step-5b: EXIT 2, 11.65 s, RSS 3079405568). Both had 12594
jobs. Explicit Polynomial R and multiplication normalization fix these
without changing any resource bound.

proof_shape content; escape_witness matchingMonomialFiberEquiv on the live
coefficient-to-polynomial-to-evaluation path; admission_basis escape-witness.
utility none for the public theorem and each of its five private helpers:
all quantify over arbitrary degrees or root families and none falls into
the four computational classes. The only frozen theorem used along this
path is coeff_additiveConvolution through the predecessor's
symmetrize_coefficient; direct frozen definition identities are itemized in
the final declaration audit. No H_0 positivity, complete parity identity,
or all-order omission of H_1 follows as a claim of this delivery.

Step 5 was pushed as `de5b6601e1`.

## Per-declaration Audit

The complete [declaration audit](matching-equiv-0908-declarations.json)
contains one entry for each of the canonical report's 234 declarations in
the four changed Lean modules. Each entry has its exact name, statement_id,
axioms, individual utility classification and reason, and frozen dependency
GID/statement_id records. Every public theorem also has proof_shape,
escape_witness, and admission_basis. This includes the 17 unchanged public
theorems in MatchingFiber and the compiler-generated congruence companions.
No imported-but-unused theorem is counted as a mathematical premise.

There are 35 authored public theorems, 49 authored private theorems, and two
compiler-generated public congruence theorems. Every one of the 84 authored
theorems has an explicit `#print axioms` in its source; a source-to-report
cross-check found zero missing prints. Their closures are exactly
`[Classical.choice, Quot.sound, propext]`. The remaining generated
declarations and definitions have closures contained in that set; no
`sorryAx` or new axiom appears in the verified report.

For every one of the 234 declarations, utility is individually `none`:
the authored declarations concern arbitrary finite types, degrees, subsets,
or root families; generated declarations support those same symbolic
operations. None enumerates a bounded set of theorem parameters, certifies
a numerical instance, implements a checker, or leaves a numerical reduction
premise. These utility and proof-shape classifications are worker
assessments, not an independent review or a machine claim of semantic
classification. SL-031 reports `semantics=unverified-by-machine`.

The following table isolates this brief's 18 new public theorems. All use
direct frozen theorem premises `none`, except that the final identity reaches
the coefficient theorem through the predecessor's local helper as described
below. Definition references are recorded separately in the JSON audit.

| Declaration | proof_shape | escape_witness | admission_basis / directed companion use |
| --- | --- | --- | --- |
| PerfectMatchingCount.card_fixedPointFreeInvolution_mul | bind-only | none | rule-11-upstream-wrapper; card_matchingMonomialFiber_mul -> this count |
| PerfectMatchingCount.card_fixedPointFreeInvolution | bind-only | none | rule-11-upstream-wrapper; card_matchingMonomialFiber -> this count |
| MatchingFiber.matching_edge_eq_of_mem | bind-only | none | companion: fiberToFactors_injective -> incidence uniqueness |
| MatchingFiber.crossPartner_mem | content | exists_cross_partner | escape-witness |
| MatchingFiber.crossPartner_eq_iff | content | exists_cross_partner and unique incidence | escape-witness |
| MatchingFiber.crossPartner_involutive | content | explicit paired cross endpoints | escape-witness |
| MatchingFiber.crossPartner_ne | content | actual loop-free cross edge | escape-witness |
| MatchingFiber.squarePartnerEmbedding_mem | content | squareChoiceEquiv recovers the chosen edge | escape-witness |
| MatchingFiber.matching_edge_cases | content | explicit square/cross decomposition of all edges | escape-witness |
| MatchingFiber.decorationExponent_injective | bind-only | none | companion: fiberToFactors_injective -> local-choice uniqueness |
| MatchingEquiv.fiberToFactors_injective | content | matching_edges_factors | escape-witness |
| MatchingEquiv.fiberToFactors_surjective | content | rebuilt_exponent and fiberToFactors_rebuilt | escape-witness |
| MatchingEquiv.card_matchingMonomialFiber | content | matchingMonomialFiberEquiv | escape-witness |
| MatchingEquiv.card_matchingMonomialFiber_mul | content | matchingMonomialFiberEquiv | escape-witness |
| MatchingEquiv.coeff_matchingSum_fiber | content | matchingMonomialFiberEquiv via the product count | escape-witness |
| MatchingPolynomial.matchingSum_esymm_mul | content | fiber equivalence, exponent classification, shifted sum | escape-witness |
| MatchingPolynomial.matchingSum_esymm | content | live proof of matchingSum_esymm_mul | escape-witness |
| MatchingPolynomial.matching_identity | content | the fiber equivalence on the coefficient/evaluation path | escape-witness |

The nontrivial equivalence is on the live proof path, not an unused import
or a discarded conjunction component. The directions are
`matching_identity -> real_matchingSum_mul -> matchingSum_esymm_mul ->
coeff_matchingSum_fiber -> card_matchingMonomialFiber_mul ->
matchingMonomialFiberEquiv`. The inverse requires both rebuilt_exponent and
fiberToFactors_rebuilt. The count cannot be obtained from just the two
factor cardinalities without that equivalence, as the mandatory probe shows
for the restricted proof attempt.

The frozen boundary reached through symmetrize_coefficient is:

| Frozen GID | statement_id |
| --- | --- |
| D5/S3/Zeros/Convolution/FiniteConvolutionCoefficients.coeff_additiveConvolution | sha256:22e74279dd95309d79b0e8a1737f0f3cc47b35cea04bebdf984da4f26e3926f7 |
| D5/S3/Zeros/Convolution/FiniteFreeCommutatorDegreeFour.dilate | sha256:cfeef8d70acd59c3974ef7fce414e3607d72c81cb6d6f9e6d41be3b66c990cee |
| D5/S3/Zeros/Convolution/FiniteFreeCommutatorDegreeFour.symmetrize | sha256:e9db27e70bca5288a1bc78fb5b5f63f1dbfc300b6b176a87a46b3231ebae4bab |
| D5/S3/Zeros/Convolution/FiniteFreeCommutatorDegreeFour.elementaryCoeff | sha256:6edacf40fa3575becc3b3548435bf99326ea1e208a06ab9255b2ff81051fe2c9 |
| D5/S3/Zeros/Convolution/FiniteFreeCommutatorDegreeFour.additiveConvolution | sha256:25a49b95cd06b2a42797145a0f0d8ea2f69fd2aad30577f099a73d629d88b267 |

These identities were cross-checked against the fresh canonical report;
the corresponding state-pin files are present. The complete source and
proof-shape assessments remain ASSUMED-UNVERIFIED by an independent seat.

## Search Receipts

All negative/positive controls below use the same supported `\b` word
boundary feature. The repository controls use the immutable pre-edit base,
so candidate declarations cannot contaminate the negative result.

```sh
git grep -n -P '\b(card_matchingMonomialFiber|card_perfectMatching|card_perfect_matching|card_fixedPointFreeInvolutions)\b' ceb8502be9e6ccabf98518284f0051b971e7104b -- D5
git grep -n -P '\b(card_partner_embeddings|squarePartnerEmbedding|MatchingMonomialFiber)\b' ceb8502be9e6ccabf98518284f0051b971e7104b -- D5/S3/Zeros/Convolution
rg -n '\b(card_fixedPointFreeInvolution|card_fixedPointFreeInvolutions|card_perfectMatching|card_perfect_matching)\b' .lake/packages/mathlib/Mathlib
rg -n '\b(card_of_cycleType_mul_eq|card_of_cycleType|doubleFactorial|card_embedding_eq|cycleType_of_pow_prime_eq_one)\b' .lake/packages/mathlib/Mathlib/GroupTheory/Perm/Centralizer.lean .lake/packages/mathlib/Mathlib/GroupTheory/Perm/Cycle/Type.lean .lake/packages/mathlib/Mathlib/Data/Nat/Factorial/DoubleFactorial.lean .lake/packages/mathlib/Mathlib/Data/Fintype/CardEmbedding.lean
```

Line-hit counts in order: **0, 7, 0, 17**; raw command exits: **1, 0, 1, 0**.
The earlier preliminary positive-count note of 31 is not used as a receipt;
17 is the mechanically recounted result for the exact final command above.
The two searched positive controls prove the word-boundary searches are
operational. Additional candidate-name checks for matchingSum_esymm,
matching_identity and exists_fiberExponent returned zero before that module
was written; their positive control on the three coefficient/factorial
theorem names returned six lines.

Online searches were actually run before the local count implementation:

| Endpoint | Query | Result |
| --- | --- | --- |
| loogle.lean-lang.org/json | `"doubleFactorial"` | 10 declarations; arithmetic API, no involution count |
| loogle.lean-lang.org/json | `"Involutive", "card"` | 1 group-homomorphism theorem, not the required permutation count |
| loogle.lean-lang.org/json | `"PerfectMatching"` | 14 declarations, no counting theorem |
| leansearch.net/search | `The number of fixed point free involutive permutations on a finite type of cardinality 2*n is the odd double factorial` | 10 related results, no exact counting theorem |

LeanSearch used POST JSON with a one-element query array and
`num_results: 10`. Raw command strings and parsed responses are retained in
`search-audit.json` in the attempt directory, extracted from the worker's
JSONL transcript. The broader local cycle-type search found
Mathlib/GroupTheory/Perm/Centralizer.lean:680 and that theorem is directly
used. DoubleFactorial arithmetic, Equiv.Perm, SimpleGraph matching APIs,
and Finset.sym2 were inspected; no recurrence was re-proved.
For the final bridge, the pinned Vieta and aeval_esymm declarations were
found locally and used directly. A missing AEval.lean filename was corrected
by searching the directory; the API lives in Algebra/MvPolynomial/Eval.lean.
No absolute nonexistence claim outside these searched scopes is made.

## Final Verification

The final Lean source hash matches the worker-produced canonical report
for all four changed Lean modules. Canonical report SHA-256:
`4ad88ef4e96216f51c5070499b6526b239960005d4e460ee49a593af2b33aec7`.

| Check | EXIT | Seconds | Maximum RSS Bytes |
| --- | --- | --- | --- |
| /usr/bin/time -l make lean (step-5c) | 0 | 17.46 | 3137781760 |
| /usr/bin/time -l make lean-report | 0 | 72.06 | 3996041216 |
| /usr/bin/time -l make emit | 0 | 59.61 | 1262092288 |
| /usr/bin/time -l make -C tools selftest | 0 | 3.90 | 251904000 |
| timed candidate admission check | 3 | 75.70 | 6578225152 |

The direct make lean reports 12594 jobs. The canonical report uses delta
mode, rechecking four modules; it does not print a separate job count.
The supervisor samples a process-tree peak of 4911232 KB for the report;
this is a different measurement from time's single-process RSS and is not
substituted for it. All timed attempts, including failures and their job
counts, are itemized in the worker-owned `build-audit.json`.

Selftest reports SELFTEST PASS, deterministic checks, and active rules
SL-001, SL-002, SL-003, SL-004, SL-006, SL-007, SL-008, SL-009, SL-010,
SL-011, SL-012, SL-013, SL-014, SL-015, SL-016, SL-017, SL-018, SL-019,
SL-020, SL-021, SL-022, SL-023, SL-025, SL-026, SL-028, SL-030, SL-031,
SL-032, SL-033, SL-034. The explicit deferred cases are SL-007:D5-T0011,
SL-009:D5-T0012, SL-013:D5-T0013, and SL-014:D5-T0010.

The admission command was:

```sh
/usr/bin/time -l dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- check --candidate-lean-report .lake/build/stratalint/raw-lean-report.json --protected-base ceb8502be9e6ccabf98518284f0051b971e7104b
```

Raw EXIT **3**, not zero. Scribe verification, Lean closure, canonicalization,
and all content-rule passes succeeded (`rule-passes: passed`). The sole
final annotation is `PROTECTED_SURFACE_CHANGE count=3`, naming the new
MatchingEquiv, MatchingPolynomial and PerfectMatchingCount `.scribe.cs`
files under Blueprint/D5/S3/Zeros/Convolution. No gate or policy was changed.
SL-031 observes utility none for all four Lean modules. SL-034 observes
missing state pins, consistent with this branch-only, no-deposit delivery.
The generated Markdown was emitted from typed Scribe; MatchingFiber.md only
gains its new imported-module dependency. No Blueprint Markdown was authored
by hand.

## Worker Artifacts

Attempt directory:
`/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/matching-equiv-0908/attempt-1`.

The worker owns the raw build logs, bind-only probe, declaration-audit.json,
build-audit.json, search-audit.json, result.json and completion.sentinel.
The result envelope has exactly conclusion and log_ref at top level, records
all pushed commits and changed paths, and is published by temporary file
plus atomic rename, followed by the same sequence for the sentinel.
No PR, freeze pin, coverage edge, independent review, H_0(R) positive
semidefiniteness, complete parity identity, or all-order H_1 omission is
claimed. The mathematical obligations in steps 1-5 are all complete.
