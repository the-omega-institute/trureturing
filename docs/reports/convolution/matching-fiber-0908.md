# Matching Fibers: CMP Equation (2)

skill: consensus-rnd:sshx
producer: one codex-cli implementation worker
independent_review: ASSUMED-UNVERIFIED (zero review seats)

Repository: https://github.com/the-omega-institute/trureturing
Worktree: /Users/auricstudio/trureturing-matching-delete-0908
Branch: lane/math/matching-delete-0908
Base: 45e7b20dd95dd8b2d7b8784392c1814193b80515
Lane: #6160; deep reasoning lane: #6377.
Lean: v4.33.0.
Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d.

## Scope

This is an incremental implementation of the user-supplied monomial-fiber route.
The target is the exact unbounded `MatchingIdentity` from
[matching-sos-0908.md](matching-sos-0908.md). No numerical experiment is a Lean premise.
The orchestrator's verification covers only the numerical readings (star), (A),
(B), (C), and (D) in the brief. All Lean readings here are worker-run.
No independent Lean review is claimed.

Proposed escape witnesses, preregistered by the brief: the subset-fiber
bijection (B), the square-edge/partner and cross-edge/perfect-matching
decomposition (C), and their live use in the full matching identity.

No positivity of H_0(R), complete parity identity, or all-order omission of H_1
is asserted.

## First Requirement: Bind-only Probe

The probe copied the archived definitions and both coefficient theorems before
attempting the exact `MatchingIdentity`. The proof attempt was:

```lean
example : MatchingIdentity := by
  intro n k hk r
  rw [symmetrize_coefficient n k hk]
  simp only [matchingSum]
  linarith only [sq_nonneg
    (∑ M : Matching n k, ∏ e ∈ M.val, edgeSquare r e)]
```

`make lean` exited 2. The coefficient theorems elaborate, each with precisely
`[propext, Classical.choice, Quot.sound]`. At probe line 101 Lean reports
`linarith failed to find a contradiction`. The remaining branch assumes the
signed elementary-coefficient convolution is strictly less than
`(sum M, prod e in M.val, edgeSquare r e) / n.descFactorial k` and asks for
`False`. The supplied square-nonnegativity fact gives no relation identifying
the two sums. No matching/coefficient bridge was found among the searched
frozen or pinned-Mathlib candidates. This is a concrete failure of this
restricted attempt, not a proof of semantic nonexistence under every encoding.

Full byte-for-byte probe: `bind-only-attempt.lean` in the artifact directory.
Log: `bind-only-make-lean.log`.
Build command: `/usr/bin/time -l make lean`.
Readings: EXIT 2; 12585 jobs; 110.73 seconds; maximum resident set size
4400988160 bytes. The temporary probe was removed before the delivered build.

## Progress

Step 1 is verified: the `Matching`, finite instance, `edgeSquare`,
`matchingSum`, `rootPolynomial`, `MatchingIdentity`, `coeff_reflection`,
and `symmetrize_coefficient` declaration bodies are copied byte-for-byte from
the archived Lean fence. Only the outer module name and header digest change.
No deposit, state pin, or coverage edge has been created.

Step 1: `/usr/bin/time -l make lean`, EXIT 0; 12585 jobs; 15.59 seconds;
maximum resident set size 2987180032 bytes. Log: `step-1-make-lean.log`.
Both public theorem `#print axioms` outputs are exactly
`[propext, Classical.choice, Quot.sound]`.

Step 1 was pushed as `01f3ada6a9`.

Step 2 is verified: `AlternatingFactorialSum.lean` is byte-for-byte identical
to the archived source fence. `/usr/bin/time -l make lean`: EXIT 0; 12586 jobs;
20.70 seconds; maximum resident set size 3015442432 bytes.
Log: `step-2-make-lean.log`. The three `#print axioms` outputs are each exactly
`[propext, Classical.choice, Quot.sound]`.

Step 2 was pushed as `8e62755894`.

Step 3 (B) is verified for arbitrary n,i,j and disjoint S,T over Q.
`coeff_esymm_mul_eq_card` identifies the coefficient with the subset-pair
fiber; `card_elementaryFiber` constructs the bijection
`U -> (S union U, S union (T \\ U))` from `T.powersetCard ell`, with inverse
`(A,B) -> A inter T`; `coeff_esymm_mul_fiber` includes all zero boundary cases.
The condition `S.card <= i` is essential when interpreting `i - S.card` in N.
Build: `/usr/bin/time -l make lean`, EXIT 0; 12586 jobs; 28.86 seconds;
maximum resident set size 3026927616 bytes. Log: `step-3b-make-lean.log`.
All three public theorem axiom prints are exactly
`[propext, Classical.choice, Quot.sound]`. The only warning is an unused
upper-bound hypothesis in `card_elementaryFiber`.

The preceding `step-3a-make-lean.log` records EXIT 2, 12586 jobs,
21.46 seconds, RSS 2978086912 bytes: two calls used `card_sdiff` where the
pinned API requires `card_sdiff_of_subset`, and the curried double sum
requires `sum_product'`. These API errors were corrected. The failed
elaboration's `sorryAx` prints are not verification evidence.

Step 3 was pushed as `b8932a62c2`.

Step 4 is partially verified. The local three-term edge expansion and the
exact decorated-matching sum now compile. Pairwise edge disjointness makes
each incident vertex exponent local. An explicit bijection between the
square choices and S proves there are exactly `S.card` square choices, so
every term in this fiber has weight `(-2 : Q) ^ (k - S.card)`. Consequently:

```lean
coeff (fiberExponent S T) (matchingSum (X : Fin n -> MvPolynomial (Fin n) Q) k)
  = (-2 : Q) ^ (k - S.card) * Fintype.card (MatchingMonomialFiber k S T)
```

The displayed formula uses ASCII abbreviations; the elaborated source is
`coeff_matchingSum_eq_card_fiber`. It is not the full factorial formula (C):
the cardinality on the right remains to be counted.
Build: `/usr/bin/time -l make lean`, EXIT 0; 12586 jobs; 22.28 seconds;
maximum resident set size 3047145472 bytes. Log: `step-4e-make-lean.log`.
All nine new public theorem axiom prints are the standard three axioms.
No resource limits were changed. The product distributivity step calls
Mathlib `Fintype.prod_sum`, whose proof inducts over the edge finset; the
only `ring` invocation added here concerns a single edge and three terms.

Failed step-4 builds, each at 12586 jobs:

| Log | EXIT | Seconds | Maximum RSS Bytes | Diagnosis |
| --- | --- | --- | --- | --- |
| step-4a-make-lean.log | 2 | 29.93 | 2998583296 | Subtype-sum rewrite failed; unsplit dependent product normalization reached the default 200000 heartbeats. |
| step-4b-make-lean.log | 2 | 20.26 | 2977087488 | Product split resolved the timeout; subtype-sum rewrite still required an explicit function argument. |
| step-4c-make-lean.log | 2 | 21.98 | 2986115072 | Constant polynomial cast required explicit map_neg/map_ofNat rewrites. |
| step-4d-make-lean.log | 2 | 20.89 | 2992832512 | Destructing a choice under dependent Option.get was ill-typed; moved the local exponent argument to a separately quantified option. |

The partial step-4 reduction was pushed as `fb494ce39a`.

The square-partner leg is now also verified. `squarePartnerEmbedding` sends
each squared vertex in S to its wasted partner in the complement of S union T;
the partner has exponent zero, and pairwise edge disjointness proves these
partners are distinct. `card_partner_embeddings` directly instantiates
Mathlib `Fintype.card_embedding_eq`, without re-proving injection counting.
Build: `/usr/bin/time -l make lean`, EXIT 0; 12586 jobs; 19.79 seconds;
maximum resident set size 3053617152 bytes. Log: `step-4g-make-lean.log`.
The three new public theorems, the two constructed equivalence/embedding
definitions, and all 14 private theorem prints have exactly the standard
three axioms. The preceding `step-4f-make-lean.log` has EXIT 2, 12586 jobs,
20.74 seconds, RSS 2994470912 bytes: `Sym2.Mem.other` required a direct call,
the complement required an explicit finset-to-sort coercion, and the
Option.get inequality required local reduction. All were corrected.

## Exact Remaining Obligation

Completed steps: 1, 2, 3. Step 4 is incomplete; steps 5 and 6 are unproved.
The missing construction is the following equivalence, under the hypotheses
shown. This is a remaining goal, not a declaration proved by this delivery:

```lean
(n k : ℕ) (hk : 2 * k ≤ n) (S T : Finset (Fin n))
(hST : Disjoint S T) (hS : S.card ≤ k) (hT : T.card = 2 * (k - S.card))
⊢ MatchingMonomialFiber k S T ≃
    ((S ↪ ↥((S ∪ T)ᶜ : Finset (Fin n))) ×
      {p : Equiv.Perm T // Function.Involutive p ∧ ∀ t, p t ≠ t})
```

The first component is `squarePartnerEmbedding`. The delivered code does not
construct the second component or a jointly inverse map. To close this goal,
one must reconstruct a loop-free, pairwise-disjoint k-edge finset from the
partner injection and cross-vertex involution, reconstruct its edge choices,
and prove both inverse laws and the prescribed exponent equality. Merely
knowing the cardinalities of the two factors does not prove this equivalence.
No marked-edge deletion/relabeling equivalence was used or attempted here.

After that equivalence, the remaining cardinality would be
`(n - S.card - T.card).descFactorial S.card * (T.card - 1).doubleFactorial`.
The first factor is locally verified; the searched TauCeti theorem supplies
the second factor only after a licensed, locally checked port. That port has
not been performed. The complete matching-fiber count (C) is therefore still
open in this attempt. This reports an implementation gap, not a mathematical
impossibility or a claim that the proposed route is invalid.

No deposit, freeze pin, coverage edge, or PR was created. The all-degree target
remains the unproved Prop `MatchingIdentity`. In particular, (A) for arbitrary
exponents outside the represented fibers, the Vieta/evaluation bridge, and
the assembly with (5) are not claimed by the partial coefficient formulas.

## Declaration Accounting

For the currently proved public theorems:

| Declaration | proof_shape | Direct Frozen Theorem Dependencies | escape_witness | admission_basis |
| --- | --- | --- | --- | --- |
| coeff_reflection | bind-only | none; unfolds frozen dilate | none | none for independent deposit; companion prerequisite of symmetrize_coefficient |
| symmetrize_coefficient | bind-only | FiniteConvolutionCoefficients.coeff_additiveConvolution | none | none for independent deposit; intended prerequisite of MatchingIdentity |
| opposite_inv_series_mul | bind-only | none (Mathlib only) | none | none for independent deposit; prerequisite of alternating_choose_convolution |
| alternating_choose_convolution | bind-only | none (Mathlib only) | none | none for independent deposit; prerequisite of alternating_factorial_sum |
| alternating_factorial_sum | bind-only | none (Mathlib only) | none | none for independent deposit; preregistered consumer is the full matching identity |
| coeff_esymm_mul_eq_card | bind-only | none (Mathlib only) | none | companion reduction for the fiber bijection; not independently deposited |
| card_elementaryFiber | content | none | explicit inverse subset-pair bijection, with injectivity and surjectivity proofs | constructive fiber counting; independent review unverified; not deposited |
| coeff_esymm_mul_fiber | content | none | subset-pair bijection plus impossibility of fibers outside the degree/cardinality guard | arbitrary-degree coefficient formula (B); independent review unverified; not deposited |
| edgeSquare_eq_choice_sum | bind-only | none | none | companion: matching_product_eq_decoration_sum -> edgeSquare_eq_choice_sum |
| matching_product_eq_decoration_sum | bind-only | none | none | companion: coeff_matchingSum_eq_decoration_fiber -> matching_product_eq_decoration_sum |
| coeff_matchingSum_eq_decoration_fiber | bind-only | none | none | companion: coeff_matchingSum_eq_card_fiber -> coeff_matchingSum_eq_decoration_fiber |
| decorationExponent_apply_of_mem | bind-only | none | none | companion: card_squareChoices_of_fiber -> decorationExponent_apply_of_mem |
| chosenSquareVertex_injective | bind-only | none | none | companion: card_squareChoices_of_fiber -> chosenSquareVertex_injective |
| card_squareChoices_of_fiber | content | none | explicit square-choice/vertex bijection; surjectivity uses nonzero exponent and the unique incident edge | escape-witness; not deposited; independent review unverified |
| decorationWeight_eq_pow | bind-only | none | none | companion: decorationWeight_of_fiber -> decorationWeight_eq_pow |
| decorationWeight_of_fiber | content | none | card_squareChoices_of_fiber is used to replace the number of square choices in the exponent | escape-witness through live square-choice bijection; not deposited |
| coeff_matchingSum_eq_card_fiber | content | none | square-choice bijection makes the weight constant on the actual coefficient fiber | escape-witness; partial (C), not full factorial count; not deposited |
| chosenSquarePartner_not_mem | content | none | locality gives exponent zero at the unused endpoint of each square choice | escape-witness on the square-partner construction path; not deposited |
| chosenSquarePartner_injective | bind-only | none | none | companion: squarePartnerEmbedding -> chosenSquarePartner_injective |
| card_partner_embeddings | bind-only | none | none | companion for the preregistered, still unproved card_matchingMonomialFiber count; not independently deposited |

The intended final consumer is `matching_identity : MatchingIdentity`; it is
not present yet. Its preregistered dependency edges are
`matching_identity -> symmetrize_coefficient -> coeff_reflection` and
`matching_identity -> alternating_factorial_sum`. The factorial module has
no independent deposit basis in this partial delivery. All `content`
classification and `escape-witness` assessments above are the implementation
worker's assessments, with independent review ASSUMED-UNVERIFIED.

The frozen theorem's GID is
`D5/S3/Zeros/Convolution/FiniteConvolutionCoefficients.coeff_additiveConvolution`.
Its recorded declaration statement_id is
`sha256:22e74279dd95309d79b0e8a1737f0f3cc47b35cea04bebdf984da4f26e3926f7`;
module pin:
`sha256:58abac734b6a8969c6215223633e21fea7d3901df1967f9531622190c058d12c`.
These identities are read from the merged predecessor report, not recomputed.

The frozen definition references are also recorded explicitly. The prefix of
each short name below is
`D5/S3/Zeros/Convolution/FiniteFreeCommutatorDegreeFour`:

| Frozen Definition | statement_id |
| --- | --- |
| dilate | sha256:cfeef8d70acd59c3974ef7fce414e3607d72c81cb6d6f9e6d41be3b66c990cee |
| symmetrize | sha256:e9db27e70bca5288a1bc78fb5b5f63f1dbfc300b6b176a87a46b3231ebae4bab |
| elementaryCoeff | sha256:6edacf40fa3575becc3b3548435bf99326ea1e208a06ab9255b2ff81051fe2c9 |
| additiveConvolution | sha256:25a49b95cd06b2a42797145a0f0d8ea2f69fd2aad30577f099a73d629d88b267 |

`coeff_reflection` references `dilate`; `symmetrize_coefficient` references
the other three definitions, the coefficient theorem, and the local
reflection lemma. The remaining public theorem proofs have no frozen
repository premise. Imported but unused frozen modules are not counted as
mathematical premises. All five frozen declaration identities above were
cross-checked against the final worker-produced canonical report and agree.

`utility: none`, assessed separately for every declaration:

| Declaration | Reason It Misses All Four Computational Classes |
| --- | --- |
| Matching | An index-type family for arbitrary n,k; no bounded instance, enumeration of parameters, checker, or numerical reduction. |
| instFintypeMatching | Finite-subtype infrastructure for every n,k; no certified instance or parameter enumeration, checker, or numerical reduction. |
| edgeSquare | A symbolic definition over every commutative ring; none of the four computational classes. |
| matchingSum | A symbolic sum for arbitrary n,k and roots; not bounded parameter enumeration, a checker, a numerical reduction, or a certified instance. |
| rootPolynomial | An arbitrary root-family product; none of the four computational classes. |
| MatchingIdentity | The unbounded target Prop, without a proof assertion; none of the four computational classes. |
| coeff_reflection | Arbitrary-degree coefficient normalization; no finite certified instance, bounded enumeration, checker, or numerical reduction. |
| symmetrize_coefficient | Arbitrary-degree symbolic identity; no finite certified instance, bounded enumeration, checker, or numerical reduction. |
| opposite_inv_series_mul | An arbitrary-power identity over every commutative ring; no parameter enumeration, checker, numerical reduction, or certified instance. |
| alternating_choose_convolution | A symbolic coefficient identity for arbitrary d,h; none of the four computational classes. |
| alternating_factorial_sum | A symbolic identity for every d,h with exact rational casts; none of the four computational classes. |
| squarefreeExponent | An exponent vector for an arbitrary finite subset; no certified instance, bounded enumeration, checker, or numerical reduction. |
| fiberExponent | A symbolic exponent vector for arbitrary S,T; none of the four computational classes. |
| squarefreeExponent_apply (private) | A general pointwise formula; none of the four computational classes. |
| fiber_pair_decomposition (private) | A general set reconstruction under an exponent equality; none of the four computational classes. |
| split_pair_exponent (private) | A symbolic exponent equality for arbitrary subsets; none of the four computational classes. |
| split_pair_inter (private) | A general set identity proving the inverse map; none of the four computational classes. |
| fiber_pair_cards (private) | Symbolic cardinalities for arbitrary finite sets; no enumeration of bounded parameters, certified instance, checker, or numerical reduction. |
| elementaryFiber | A parameterized finite fiber, not an enumeration over bounded theorem parameters; no certified instance, checker, or numerical reduction. |
| mem_elementaryFiber (private) | Symbolic fiber membership for arbitrary n,i,j; none of the four computational classes. |
| coeff_esymm_mul_eq_card | A universally quantified coefficient identity; no certified instance, bounded parameter enumeration, checker, or numerical reduction. |
| card_elementaryFiber | A universally quantified fiber cardinality theorem; none of the four computational classes. |
| coeff_esymm_mul_fiber | A universally quantified coefficient formula, including impossible cases; none of the four computational classes. |
| EdgeChoice | Symbolic local monomial indexing for arbitrary n,e; no bounded parameter enumeration, certified instance, checker, or numerical reduction. |
| edgeChoiceExponent | A symbolic exponent definition; none of the four computational classes. |
| edgeChoiceWeight | A symbolic weight definition; none of the four computational classes. |
| edgeSquare_eq_choice_sum | A generic polynomial expansion at every edge; none of the four computational classes. |
| MatchingDecoration | Symbolic indexing at every matching size; no bounded enumeration of theorem parameters, certified instance, checker, or numerical reduction. |
| decorationExponent | A symbolic exponent sum; none of the four computational classes. |
| decorationWeight | A symbolic rational weight product; none of the four computational classes. |
| matching_product_eq_decoration_sum | General finite-product identity; none of the four computational classes. |
| coeff_matchingSum_eq_decoration_fiber | Arbitrary-degree coefficient identity; none of the four computational classes. |
| edgeChoiceExponent_zero_of_not_mem (private) | General support fact; none of the four computational classes. |
| decorationExponent_apply_of_mem | General locality theorem for disjoint supports; none of the four computational classes. |
| exists_edge_of_decorationExponent_ne_zero (private) | General incidence existence from a nonzero exponent; none of the four computational classes. |
| fiberExponent_eq_two_iff (private) | General exponent membership characterization; none of the four computational classes. |
| SquareChoices | Parameterized subset of choices, not bounded enumeration of theorem parameters; no certified instance, checker, or numerical reduction. |
| chosenSquareVertex | A symbolic map to an index; none of the four computational classes. |
| chosenSquareVertex_mem (private) | General membership projection; none of the four computational classes. |
| chosenSquareVertex_exponent (private) | General local exponent identity; none of the four computational classes. |
| chosenSquareVertex_injective | General injectivity proof; none of the four computational classes. |
| card_squareChoices_of_fiber | General symbolic cardinality from a bijection; none of the four computational classes. |
| decorationWeight_eq_pow | General symbolic weight formula; none of the four computational classes. |
| decorationWeight_of_fiber | General fiber-weight identity; none of the four computational classes. |
| MatchingMonomialFiber | A finite type parameterized by arbitrary n,k,S,T; not bounded parameter enumeration, certified instance, checker, or numerical reduction. |
| coeff_matchingSum_eq_card_fiber | General symbolic coefficient identity; none of the four computational classes. |
| chosenSquarePartner | A general endpoint map; none of the four computational classes. |
| chosenSquarePartner_mem (private) | General endpoint membership; none of the four computational classes. |
| chosenSquarePartner_ne (private) | General no-loop consequence; none of the four computational classes. |
| chosenSquarePartner_exponent (private) | General zero-exponent statement; none of the four computational classes. |
| chosenSquarePartner_not_mem | General exclusion from symbolic monomial support; none of the four computational classes. |
| chosenSquarePartner_injective | General injectivity of a map on arbitrary matchings; none of the four computational classes. |
| squareChoiceEquiv | A bijection for arbitrary n,k,S,T, without bounded parameter enumeration, certified instance, checker, or numerical reduction. |
| squarePartnerEmbedding | A constructed embedding for arbitrary fibers; none of the four computational classes. |
| card_partner_embeddings | A symbolic cardinality identity at arbitrary n,S,T; none of the four computational classes. |
| edgeChoiceExponent.match_1 (compiler-generated) | Generic pattern-match eliminator for symbolic choices; none of the four computational classes. |
| edgeChoiceExponent.match_1.splitter (compiler-generated, private) | Generic case-split support for the same definition; none of the four computational classes. |

Other utility fields are `not-applicable(kind=none)`.

## Search Receipt

Before candidate declarations were created, the following commands used the
same regex word-boundary feature, `\\b`, for negative and positive controls:

```sh
rg -n '\b(MatchingIdentity|matchingSum|symmetrize_matching_sos|matching_fiber)\b' D5
rg -n '\b(coeff_additiveConvolution|symmetrize)\b' D5/S3/Zeros/Convolution
rg -n '\b(matchingPolynomial|matching_polynomial|matchingSum|symmetrize_matching_sos|card_perfectMatching|card_perfect_matching)\b' .lake/packages/mathlib/Mathlib
rg -n '\b(IsMatching|doubleFactorial|coeff_prod_X_sub_C|esymm)\b' .lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Matching.lean .lake/packages/mathlib/Mathlib/Data/Nat/Factorial/DoubleFactorial.lean .lake/packages/mathlib/Mathlib/Algebra/Polynomial .lake/packages/mathlib/Mathlib/Algebra/MvPolynomial
```

Line-hit counts, respectively: 0, 23, 0, 53. A commentary initially said 22
for the repository positive control; the captured count is 23.

Additional reads: Mathlib `SimpleGraph.Subgraph.IsMatching`,
`IsPerfectMatching.even_card`, `Finset.sym2`, `Finset.card_sym2`,
`Sym2.card_toFinset_of_not_isDiag`, the double-factorial API,
`MvPolynomial.esymm_eq_sum_monomial`, and Vieta. The matching predicates
and edge-count APIs do not count all perfect matchings. The existing symmetric
polynomial and factorial APIs will be reused.

Network search is operational: `gh search code '"invOneSubPow" language:Lean'`
returned three requested positive-control results; `"matching_polynomial"`
returned zero. The query `"doubleFactorial" "Matching" language:Lean` found
TauCeti's `card_perfectMatching`, a candidate for (C). Its source at immutable
revision `f6f910c48c3b832f64090230c1d623c1a98a9b58` is Apache-2.0, uses only
three Mathlib imports, and pins Lean v4.34.0-rc2 / Mathlib
`e21ec05048292b3de86d4cf1987e2208171a5642`. Those differ from this tree:
direct package dependency is unavailable; any later reuse must be a licensed
port under A17.2, with its own local Lean check. No such port is yet claimed.

`dominating_theorem_search: not-found-in-searched-scope` for the full target.
Absolute nonexistence outside these searched names/candidates is
`ASSUMED-UNVERIFIED`.

## Artifact Directory

`/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/matching-fiber-0908/attempt-1`

The cache was prepared by `make lean-cache-ensure`: seeded by clonefile from
`/Users/auricstudio/trureturing`, clonefile_attempts=1, both Mathlib and project
olean states warm. Every subsequent Lean build uses the canonical make entry.
No bare lake invocation, resource-limit increase, or constant change is used.

## Final Verification

The square-partner implementation was pushed as `30932eaa98`.
An exact comparison against the predecessor's Lean fences returned:
`alternatingFactorialSum_byte_equal=true` (4935 bytes) and
`matching_skeleton_byte_equal=true` (2788-byte declaration/axiom-print segment).

`make -C tools selftest`: EXIT 0, `SELFTEST PASS`, 4.98 seconds, RSS 258244608
bytes. The deterministic two-run comparison passed. Reported rule set:
SL-001, SL-002, SL-003, SL-004, SL-006, SL-007, SL-008, SL-009, SL-010,
SL-011, SL-012, SL-013, SL-014, SL-015, SL-016, SL-017, SL-018, SL-019,
SL-020, SL-021, SL-022, SL-023, SL-025, SL-026, SL-028, SL-030, SL-031,
SL-032, SL-033, SL-034. Explicit deferred rules: SL-007:D5-T0011,
SL-009:D5-T0012, SL-013:D5-T0013, SL-014:D5-T0010.
Log: `final-selftest.log`.

`/usr/bin/time -l make lean-report`: EXIT 0; 436.58 seconds; maximum resident
set size 15978823680 bytes. The inspector's internal build reports 12586 jobs.
The supervisor separately samples a process-tree RSS maximum of 16644592 KB;
this differs in scope from `/usr/bin/time`'s single-process maximum, and is
not silently substituted for it. Log: `final-lean-report.log`.
Canonical report SHA-256:
`8f93267c69191825e2f17ad928c2dc8451cab8ade978ad875eaf873248bd84ee`.
That report contains 20 public theorem declarations, 14 private theorem
declarations, 21 authored definitions/abbreviations/instances, and two
compiler-generated match declarations for these modules. All theorem axiom
closures equal `[Classical.choice, Quot.sound, propext]`; all other declaration
closures are subsets of those three. No `sorryAx` or private axiom is present.
Per-declaration utility accounting covers all 57 declarations; the two
compiler-generated declarations inherit the symbolic, unbounded scope of
`edgeChoiceExponent`.

The first admission check used the immutable base
`45e7b20dd95dd8b2d7b8784392c1814193b80515`:

```sh
dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- check --candidate-lean-report .lake/build/stratalint/raw-lean-report.json --protected-base 45e7b20dd95dd8b2d7b8784392c1814193b80515
```

EXIT 1, 54.48 seconds, RSS 2056552448 bytes, four rejections:
SL-004 missing Blueprint mirrors for both new Lean modules; SL-010 because
the initial `G` header of MatchingFiber imports the two frozen `I` modules.
Log: `final-admission.log`. SL-031 utility admission passed in this run.
The repair re-routed MatchingFiber as `I` and added typed Scribe definitions
for both Blueprint mirrors. This changes no theorem statement or proof body,
and generality metadata is separate from the per-declaration utility class.
Neither full MatchingIdentity nor the unevaluated matching-fiber count is
presented as a theorem in the mirrors.

After the metadata repair, `/usr/bin/time -l make lean`: EXIT 0; 12586 jobs;
22.71 seconds; maximum resident set size 3054501888 bytes.
Log: `admission-fix-make-lean.log`. Every printed axiom closure remains the
standard three.

The fresh `/usr/bin/time -l make lean-report` passed: EXIT 0, 64.87 seconds,
RSS 3969466368 bytes, canonical delta mode with two modules rechecked.
Log: `admission-fix-lean-report.log`. Report SHA-256:
`241cedb75f18cac07606fb10ce782cf9b079873d491935e2fc1343cd102906d8`.
All 57 declaration statement IDs and axiom closures equal those in the
preceding report; both current source hashes match the current Lean files.

`/usr/bin/time -l make emit`: EXIT 0, 56.55 seconds, RSS 1262993408 bytes.
Log: `final-emit.log`. Exactly two Blueprint documents changed. They were
emitted from the typed Scribe definitions; no Blueprint Markdown was authored
by hand. Other generated projections are ignored run-local output, and no
unrelated tracked path changed.

Admission recheck with the same command and immutable base: EXIT 3,
84.29 seconds, RSS 6600245248 bytes. Log: `admission-recheck.log`.
Every content-rule stage, Scribe verification, Lean closure, and canonicalization
passed; `rule-passes` reports `status=passed`. The only final classification is
`PROTECTED_SURFACE_CHANGE count=2`, naming the two new `.scribe.cs` files.
Per `CLAUDE.md:543` and spec A16, this is the SL-022 annotation with content
checks passed; it is not reported here as raw EXIT 0. No rule or gate was changed.
SL-031 reports `UTILITY-OBSERVED kind=none semantics=unverified-by-machine`
for both modules. SL-034 observes missing frozen state pins, consistent with
this delivery's explicit no-deposit status. The deferred rule list is the same
four cases printed by selftest.

Worker artifacts include `declaration-audit.json` (57 declarations with utility
reasoning, exact statement IDs, and axiom closures), `build-audit.json`, and
the strict `result.json` envelope. The implementation conclusion is partial:
steps 1-3 complete, step 4's weighted reduction and square-partner leg verified,
full step 4 count and steps 5-6 still open. The result envelope records all pushed
commit IDs and the complete changed-path list. No independent review is claimed.
