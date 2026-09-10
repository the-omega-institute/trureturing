# CMP Conjecture 3.13, degree three attempt (2026-09-09)

skill: consensus-rnd:sshx
producer: one codex-cli implementation worker
independent_review: ASSUMED-UNVERIFIED

Scope: second-tier, fixed m=3 and every real alpha > -1, under #6494 / #6160.
The task does not assert the general-m conjecture, a solution of Conjecture
3.13, or worldwide priority. The orchestrator verified only the m=2 interface,
the earlier name-search absence, and the paper quotation/page. All new Lean
and search observations are this implementation worker's own measurements.

## Preregistered Attempt

First attempt: only pinned Mathlib instantiation, frozen projection, and
normalization, including square nonnegativity and `linarith only`. Stop and
report bind-only if that proves the main goal; do not create a content module.
The initial probe is temporary and is not a deposit candidate.

Proposed escape witness, only if the first attempt fails: a quantitative
nonnegative decomposition or bound for the cubic output discriminant over
the full six-root domain and alpha > -1. The exact candidate is
`S^2*T^2 - 4*T^3 - 4*S^3*U - 27*U^2 + 18*S*T*U >= 0`, where
`S = A1+B1`, `T = A2+B2+2*(alpha+2)/(3*(alpha+3))*A1*B1`, and
`U = A3+B3+(alpha+1)/(3*(alpha+3))*(A1*B2+A2*B1)`.
Here Aj and Bj are the elementary symmetric coefficients of the two input
root triples. Definitions and coefficient signs are expected bind-only.

The frozen consumer already found is
`D5/S3/Zeros/Convolution/FiniteFreeCommutatorDegreeSix.cubic_nonnegative_factorization`.
It requires exactly the three coefficient signs and this discriminant sign.
No reconstruction theorem will be reproved.

Stop criteria: a successful bind-only proof; all five requested steps checked;
or a documented mathematical/cost obstruction after splitting the failed
algebraic block. No heartbeat, recursion, constant, or toolchain changes.
Each completed part is committed and pushed. No PR is to be opened.

## Initial Evidence

Initial worktree: clean, branch `lane/math/gribinski-m3-0909` tracking
`origin/dev`. Lean v4.33.0; Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`.
Frozen m=2 module state: `sha256:184c298cb6b3a6b32640e84511f41eede52d8d0d29ae2b24a68f14ef5722487e`.

Repository textual search receipts, before introducing this report:

| Command | Matching lines | Exit |
| --- | ---: | ---: |
| `rg -n '\bGribinskiDegreeThree\b' D5 Blueprint Golden` | 0 | 1 |
| `rg -n '\bg3_nonnegative_roots\b' D5/S3/Zeros/Convolution/GribinskiDegreeTwo.lean` | 3 | 0 |
| `rg -n -i '\b(gribinski\|boxplus\|rectangular.*convolution)\b' .lake/packages/mathlib/Mathlib --glob '*.lean'` (alternation uses unescaped pipes) | 0 | 1 |

The same word-boundary feature has a positive control: the pinned Pochhammer
file contains `descPochhammer`, including its evaluation positivity theorem.
These are textual search observations, not semantic completeness claims.

Loogle `Cubic.discr` returned 11 declarations; the available discriminant
root-product theorem assumes splitting and therefore cannot supply splitting
for this output. Literature recheck and complete verification receipts follow
with the implementation results.

## Bind-Only Probe Result

The first restricted attempt failed exactly at the discriminant obligation;
the frozen factorization theorem applied and all three sign obligations closed.
This is failure of this attempted proof, not proof that no bind-only proof exists.
Temporary source and full log are in the runner attempt directory as
`bind-only.lean` and `bind-only.log`. The temporary D5 probe was removed.

Raw Lean diagnostic:

```text
error: D5/GribinskiM3BindProbe.lean:30:4: linarith failed to find a contradiction
case hd
alpha a b c d e f : Real
halpha : -1 < alpha
ha : 0 <= a
hb : 0 <= b
hc : 0 <= c
hd : 0 <= d
he : 0 <= e
hf : 0 <= f
```

The remaining contradiction assumption is exactly the negative of the
preregistered cubic discriminant above; the complete pretty-printed goal is
retained verbatim in `bind-only.log`.

`/usr/bin/time -l make lean`: EXIT=2, last job denominator=12680,
39.22 real seconds, maximum resident set size=3513860096 bytes.
The probe itself was reported as 18s. Cache receipt: status=present,
method=none, project_olean_state=warm, mathlib_olean_state=warm.
The full command builds the requested tree and includes unrelated cached
diagnostics and incremental builds; RSS is not claimed to isolate the probe.

## Step 1

The degree-three definition layer and `definition_consistency` are checked.
`/usr/bin/time -l make lean`: EXIT=0, 12680 jobs, 19.41 seconds,
maximum resident set size=2978545664 bytes (`step1-fixed.log`).
Initial simplification left `-((-1)^3 * cc3) = cc3` unresolved
(`step1.log`: EXIT=2, 18.61s, RSS=2927116288); `norm_num` closed it.

| Declaration | proof_shape | escape_witness | admission_basis | utility |
| --- | --- | --- | --- | --- |
| elementaryCoeff | not-applicable(definition) | none | none | Symbolic degree-three coefficient convention; kind=none |
| weight | not-applicable(definition) | none | none | Product prefactor in Definition 3.10; kind=none |
| normalizedCoeff | not-applicable(definition) | none | none | Symbolic normalization; kind=none |
| convolutionCoeff | not-applicable(definition) | none | none | General coefficient convolution; kind=none |
| boxplus3 | not-applicable(definition) | none | none | Reconstruction of the four coefficients; kind=none |
| rootTriple | not-applicable(definition) | none | none | Three arbitrary real linear factors; kind=none |
| definition_consistency | bind-only | none | none | Definition 3.10 coefficient agreement for arbitrary inputs; kind=none |

`#print axioms definition_consistency`: `[propext, Classical.choice, Quot.sound]`.
Direct frozen dependencies of Step 1: none. No declaration is finite
enumeration, a certified numerical instance, a checker, or a numerical
reduction; all are symbolic definitions or identities. The module is unfrozen
and no deposit admission basis is claimed for this stage.

## Step 2

The four explicit coefficient formulas and the resulting cubic are checked.
The cross weights are `kappa = 2*(alpha+2)/(3*(alpha+3))` and
`rho = (alpha+1)/(3*(alpha+3))`. This identity holds whenever alpha avoids
-1, -2, and -3, before any nonnegative-root assumptions.

`/usr/bin/time -l make lean`: EXIT=0, 12680 jobs, 19.08 seconds,
maximum resident set size=3026436096 bytes (`step2.log`).
Step 1 commit: `60254ff432`, pushed to the requested branch.

| Declaration | proof_shape | escape_witness | admission_basis | utility |
| --- | --- | --- | --- | --- |
| kappa | not-applicable(definition) | none | none | Second-coefficient cross weight; kind=none |
| rho | not-applicable(definition) | none | none | Third-coefficient cross weight; kind=none |
| convolution_coefficients | bind-only | none | none | Definition 3.10 specialized to two arbitrary root triples; kind=none |
| m3_explicit_coefficients | bind-only | none | none | Polynomial identity consumed by the root/discriminant obligations; kind=none |

Private helpers `weight_values` and `rootTriple_coefficients` are bind-only
normalization. The latter uses `Cubic.prod_X_sub_C_eq` directly.
Direct frozen dependencies: none. The actual companion edge is
`m3_explicit_coefficients -> convolution_coefficients`.
Each of the three public theorems prints exactly
`[propext, Classical.choice, Quot.sound]` in `step2.log`.

## Step 3

`weight_pos` and `m3_nonnegative_coefficients` are checked on the entire
alpha > -1 and nonnegative-root domain. They are bind-only, with no escape
witness or admission basis. The weight proof directly instantiates pinned
Mathlib `descPochhammer_pos`; the three signs use the explicit formulas.
Both have utility kind=none (symbolic parameter inequalities).
Actual edge: `m3_nonnegative_coefficients -> convolution_coefficients` and
`m3_nonnegative_coefficients -> definition_consistency`.
`weight_pos` records positivity of the original Definition 3.10 prefactors;
it is not claimed as an escape-path prerequisite.

`/usr/bin/time -l make lean`: EXIT=0, 12680 jobs, 18.97 seconds,
maximum resident set size=3034939392 bytes (`step3.log`).
All five public theorems print `[propext, Classical.choice, Quot.sound]`.
Step 2 commit: `e6f61716af`, pushed.

## Discriminant Exploration

Exact SymPy 1.14.0 probe, not a kernel proof: write the ordered roots as
`x,x+u,x+u+v` and `y,y+w,y+w+z`, and set `t=alpha+1`.
Then `27*(alpha+3)^3*Delta` has 787 monomials, by t-degree
`310,257,168,52`. Exactly 20 coefficients are negative.
A subtraction of 20 weighted squares leaves 767 positive monomials and
no negative coefficients; the reconstruction equality was checked by exact
rational polynomial arithmetic. Source: runner `discriminant-probe.py`;
successful output: `discriminant-probe-complete.log`.
Two earlier diagnostic-count runs failed on SymPy Boolean conversion;
they supplied no completed diagnostic result. The exact polynomial equality
assertion passed in the successful run. This proposes a split certificate
for the already preregistered discriminant witness, not a new target.

## Attempt 2: Resumption and Certificate

Continuation producer: one codex-cli implementation worker, no additional
skill invoked by this worker and no review seats. The enclosing runner context
remains `consensus-rnd:sshx`; independent_review: ASSUMED-UNVERIFIED.
The requested branch was clean and synchronized at `d625f554ae`; Steps 1--3
are retained without redoing their proofs. The three earlier pushed commits
are `60254ff432`, `e6f61716af`, and `d625f554ae`.

Current textual controls, before adding the certificate module:

| Command | Matching lines | Exit |
| --- | ---: | ---: |
| `rg -n '\bGribinskiDegreeThree\b' D5 Blueprint Golden` | 4 | 0 |
| `rg -n '\bcubic_nonnegative_factorization\b' D5/S3/Zeros/Convolution/FiniteFreeCommutatorDegreeSix.lean` | 3 | 0 |
| `rg -n '\b(rootTriple\|sorted.*triple\|triple.*sorted)\b' D5 --glob '*.lean'` (unescaped alternation pipes) | 14 | 0 |

The former negative control now names our existing module; it is not reported
as an absence. Both controls use the same `rg` word-boundary feature.
The retained exact probe and successful stdout in attempt-1 were read.
For actual Lean consumption, `attempt-2/emit-certificate.py` emits the same
20-square/767-positive-monomial certificate in multivariate Horner form.
The generator is untrusted: all four equalities and all signs are proved in
Lean. No change to `maxHeartbeats`, `maxRecDepth`, mathematical constants,
or the toolchain was made.

`GribinskiDegreeThreeDiscriminant.numerator` is the cleared discriminant with
denominator `6+3*t`, T numerator `a+b*t`, and U numerator `c+d*t`.
The four coefficient identities are checked separately, then assembled by
`numerator_expansion`. Each `sosN` is the positive remainder plus the retained
weighted squares of that t-degree. The highest coefficient is independent of
the two least roots, so the corresponding unused-variable warnings are benign.

| Command/log (attempt-2) | EXIT | Jobs | Real seconds | Maximum RSS bytes |
| --- | ---: | ---: | ---: | ---: |
| `/usr/bin/time -l make lean`, `certificate-1.log` | 2 | 12681 | 53.33 | 7384252416 |
| `/usr/bin/time -l make lean`, `certificate-2.log` | 0 | 12681 | 64.18 | 7801700352 |

Both cache receipts are `present`, `method=none`, project/mathlib `warm`.
These are full incremental make-process measurements, not isolated theorem
benchmarks. In the first build all four ring identities passed; the subsequent
`positivity` calls for coefficients 0 and 1 exhausted the default 200000
heartbeats (lines 147 and 225 of that candidate). Splitting identities and
signs into separate declarations resolved this without increasing budgets.
The failed build's `sorryAx` diagnostic is not an accepted proof; the second
build prints only `[propext, Classical.choice, Quot.sound]` for every theorem.

| Public declaration | proof_shape | escape_witness | admission_basis | utility |
| --- | --- | --- | --- | --- |
| `GribinskiDegreeThreeDiscriminant.numerator` | not-applicable(definition) | none | companion to certificate | symbolic discriminant expression; kind=none |
| `GribinskiDegreeThreeDiscriminant.ordered_numerator_nonneg` | content | four `coeffN_identity` equalities with `sosN_nonneg`, assembled by `numerator_expansion` | escape-witness | universal real-parameter inequality for Step 4; kind=none |

The certificate is a symbolic inequality for every nonnegative real tuple,
not a bounded enumeration, checker, certified input instance, or numerical
reduction. Its new decomposition lies on the live proof path: all four
coefficient signs are multiplied by powers of t and added. Removing those
signs leaves the discriminant sign unproved; no frozen premise supplies it.
It is not a restatement of the final root factorization. Direct frozen
dependencies of this certificate: none; only pinned Mathlib is imported.
`#print axioms` includes the public theorem and all thirteen private theorems
(four identities, four SOS signs, four coefficient signs, parameter expansion).

At this checkpoint Step 4 is still incomplete: this theorem covers ordered-gap
coordinates. The next obligation is to express any nonnegative root triple in
these coordinates up to equality of its polynomial, then clear denominators
and connect the result to the original coefficient convolution.

## Step 4: Full Root Domain

Certificate checkpoint `ab7fd079b0` was pushed successfully. Step 4 is now
proved by `GribinskiDegreeThree.m3_discriminant_nonneg`. Its hypotheses are
exactly six nonnegative real roots and `alpha > -1`; no ordering, distinctness,
strict root positivity, or additional parameter restriction is assumed.

`nonnegative_rootTriple_coordinates` proves that each nonnegative triple has
the same polynomial as `rootTriple x (x+u) (x+u+v)` with x,u,v nonnegative.
The proof covers all six weak orderings using `le_total`, then chooses
`x=r`, `u=s-r`, `v=t-s` for a sorted triple r,s,t. Factor commutativity proves
polynomial equality. The main theorem invokes this result separately on both
input triples and rewrites both input polynomials before applying the
certificate. Thus the previously identified coordinate-image gap is closed.

The scalar bridge `discriminant_numerator` proves exactly
`27*(alpha+3)^3*Delta = numerator (alpha+1) S (6P+2Q) (3P+2Q) (6R) (3R+V)`,
where T=P+kappa*Q and U=R+rho*V. Substitution uses
P=A2+B2, Q=A1*B1, R=A3+B3, V=A1*B2+A2*B1. Since alpha+3 is positive,
the cleared sign implies the original cubic discriminant sign. The bridge to
the input operation uses `definition_consistency` and
`convolution_coefficients`, so the certificate is connected to Definition 3.10.

| Public declaration | proof_shape | escape_witness | admission_basis | utility |
| --- | --- | --- | --- | --- |
| `discriminant` | not-applicable(definition) | none | not-applicable(definition) | signed monic cubic coefficient discriminant; kind=none |
| `nonnegative_rootTriple_coordinates` | bind-only | none | escape-witness, companion within this content module | coordinate coverage obligation; kind=none |
| `m3_discriminant_nonneg` | content | the live four-coefficient SOS certificate, plus coverage of both arbitrary triples | escape-witness | full symbolic discriminant sign for Step 5; kind=none |

The coordinate construction is conservatively classified bind-only: its six
order cases use pinned order dichotomy and arithmetic normalization. It is
not asserted to justify an independent freeze. Actual consumer-to-prerequisite
edges are `m3_discriminant_nonneg -> nonnegative_rootTriple_coordinates` and
`m3_discriminant_nonneg -> ordered_output_discriminant -> ordered_numerator_nonneg`.
The latter also consumes the scalar clearing identity and the original
coefficient formulas. Direct frozen dependencies for Step 4: none.

New pinned upstream lookup receipts: `le_total` in
`Mathlib/Order/Defs/LinearOrder.lean:92`, and
`nonneg_of_mul_nonneg_right` in
`Mathlib/Algebra/Order/Ring/Unbundled/Basic.lean:346` are used directly.
Search commands: `rg -n '\b(sort_perm\|perm_sort\|le_total)\b'` on the pinned
List/Sort and Order/Defs/LinearOrder files gave 6 matching lines (all in the
latter); `rg -n 'theorem nonneg_of_mul_nonneg_(left\|right)\|lemma nonneg_of_mul_nonneg_(left\|right)'`
on pinned Mathlib/Algebra/Order with `--glob '*.lean'` gave 2 lines. Both
commands used unescaped alternation pipes; EXIT=0. These are local source
lookups, subsequently validated by Lean applications, not absence claims.

| Command/log (attempt-2) | EXIT | Jobs | Real seconds | Maximum RSS bytes |
| --- | ---: | ---: | ---: | ---: |
| `/usr/bin/time -l make lean`, `step4-1.log` | 2 | 12681 | 18.42 | 3034906624 |
| `/usr/bin/time -l make lean`, `step4-2.log` | 0 | 12681 | 21.40 | 3094347776 |

The first build already proved the coordinate lemma and scalar identity; its
only error was rewrite matching at the certificate bridge, caused by addition
and multiplication association. `simp only [mul_assoc, add_assoc]` aligned
the expressions. The successful build prints standard three-axiom closures
for all seven public theorems in the main module and both new private helpers;
the certificate's fourteen theorem closures remain standard three-axiom.
Both caches are warm; the one coordinate-tactic style warning is nonsemantic.

## Step 5: Nonnegative Roots

Step 4 commit `d714993877` was pushed. The requested theorem
`GribinskiDegreeThree.m3_nonnegative_roots` is now kernel-checked:

```lean
theorem m3_nonnegative_roots (alpha a b c d e f : Real) (halpha : -1 < alpha)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c)
    (hd : 0 <= d) (he : 0 <= e) (hf : 0 <= f) :
    ∃ r s t : Real, 0 <= r ∧ 0 <= s ∧ 0 <= t ∧
      boxplus3 alpha (rootTriple a b c) (rootTriple d e f) = rootTriple r s t
```

The proof applies the already frozen
`D5/S3/Zeros/Convolution/FiniteFreeCommutatorDegreeSix.cubic_nonnegative_factorization`
directly to Step 3 and Step 4, then reconstructs the polynomial using the
original coefficient definition and its leading coefficient 1. The frozen
module's state pin is
`sha256:c432340052440ba09b56af8739b2dee5b23e520877aa3593410b92b1dbad9daf`.
No root reconstruction theorem was reproved.

| Public declaration | proof_shape | escape_witness | admission_basis | utility |
| --- | --- | --- | --- | --- |
| `m3_nonnegative_roots` | content | the four-coefficient discriminant certificate consumed through `m3_discriminant_nonneg` | escape-witness | preservation for every six-root tuple and alpha > -1; kind=none |

The final assembly is a thin application of the frozen factorization theorem;
the whole proof is content after inlining its newly proved prerequisites.
Its discriminant premise is supplied by the live new SOS certificate, not by
a frozen hypothesis. The proof contains no dead certificate term or discarded
conjunct. Consumer-to-prerequisite edges:
`m3_nonnegative_roots -> m3_nonnegative_coefficients`,
`m3_nonnegative_roots -> m3_discriminant_nonneg`, and
`m3_nonnegative_roots -> cubic_nonnegative_factorization`.

The earlier five public theorems retain their bind-only classifications.
For this combined content delivery they are named companions under the
module's `escape-witness` basis; their own escape_witness remains none.
`definition_consistency` and `convolution_coefficients` are live prerequisites
of Steps 3--5; `m3_explicit_coefficients` is the explicitly preregistered
Step 2 obligation, and `weight_pos` is the explicitly preregistered Step 3
weight-domain obligation. Neither of the latter two is misrepresented as a
live escape prerequisite. Definitions have no independent admission basis;
the earlier certificate-table phrase "companion to certificate" refers to
that role, not to a fourth allowed basis. No `refutes` basis is used.

| Command/log (attempt-2) | EXIT | Jobs | Real seconds | Maximum RSS bytes |
| --- | ---: | ---: | ---: | ---: |
| `/usr/bin/time -l make lean`, `step5-1.log` | 2 | 12681 | 20.76 | 3044573184 |
| `/usr/bin/time -l make lean`, `step5-2.log` | 0 | 12681 | 19.71 | 3097346048 |

The first assembly build obtained the three nonnegative roots but left the
final polynomial equality open after unnecessarily unfolding both input
`rootTriple` definitions. Using `change` only on the result shape fixed the
syntactic match. The successful build prints all eight public and all four
private main-module theorem closures, each exactly
`[propext, Classical.choice, Quot.sound]`. Together with the certificate this
accounts for 26 theorem printouts, including all 9 public theorems.
The certificate's four benign unused-variable warnings remain; the main
module has no new warning in the final build.

## Explicit Nonclaims

All five requested mathematical steps are proved, with Steps 1--3 inherited
and Steps 4--5 completed here. This is only the fixed m=3, second-tier slice.
It does not prove general m, solve Conjecture 3.13 in full, or claim priority.
As of 2026-09-09, the retained searches did not locate an answer covering m=3
and every alpha > -1; this is a search observation, not a nonexistence proof.
The previous attempt's literature and Loogle receipts were reused as requested:
`loogle-cubic.json` contains 11 hits, `loogle-discrim.json` 14, and
`loogle-pochhammer.json` 43. The retained Campbell--Jalowy HTML contains the
"It appears open whether ... preserves positive roots for non-integer ..."
passage at line 1220; the #6494 qualification comment is
https://github.com/the-omega-institute/trureturing/issues/6494#issuecomment-5590690493.

independent_review: ASSUMED-UNVERIFIED. These are this implementation worker's
local observations, not orchestrator revalidation or independent review.
No PR, merge, deposit, freeze, coverage update, or CI approval is claimed.
The two modules are delivered unfrozen on the requested branch. Their stated
escape-witness basis is the worker's proof-shape assessment for review, not a
claim that the soft admission semantics have been independently approved.

## Final Semantic Verification

Step 5 commit `1b046a2d6c169fea247611f2c16d375ebb79e821` was pushed
successfully. The final Lean source tree is unchanged after its successful
build. `/usr/bin/time -l make lean-report` then exited 0 in 69.71 seconds,
with maximum RSS 4773314560 bytes (`attempt-2/lean-report.log`). Its cache
receipt is `present`, `method=none`, with both project and Mathlib warm.
The inspector delta was `changed=0 added=27 removed=0 recheck=27` relative
to the retained semantic-report cache; this is not the task's Git diff.

Canonical report: `.lake/build/stratalint/raw-lean-report.json`.
Report SHA-256:
`20b925ef0ef86b656f60079b914364b66292344a31b3ab47ea941c67d6735b09`.
Input address:
`sha256:a20ab3bd7c3261e58c6f85f9c399e3b5a3f61e6b30d117bbc35fa45374ae880d`.
The producer provenance is the adjacent
`raw-lean-report.json.provenance.json`. Both task modules occur in this
report, and `shasum -a 256` matches their recorded source hashes:

| Module | Source SHA-256 |
| --- | --- |
| `GribinskiDegreeThree` | `sha256:f27173bbe2739f8fee728450cad1388f56750656d624610ce90c66f2345d12a6` |
| `GribinskiDegreeThreeDiscriminant` | `sha256:bcbd16debca04f7147021418b09cc0c4cbd34fc33bfd6e02db505d13cbb341b6` |

The direct frozen prerequisite of `m3_nonnegative_roots` has GID
`D5/S3/Zeros/Convolution/FiniteFreeCommutatorDegreeSix.cubic_nonnegative_factorization`
and declaration statement_id
`sha256:984112c0a61e8d34b039bb6d01a1e73d4e1f57b7fb36b42fbd569cc818100618`.
This declaration identity is distinct from the frozen module state pin
recorded above. It is the only direct frozen public-theorem prerequisite
of the new main target; the other public theorems have no direct frozen
public-theorem prerequisites. Pinned Mathlib is not counted as a frozen GID.

All 26 explicit theorem printouts agree with the semantic report. In the
following tables, each entry records that theorem's own `#print axioms`
result, not an inference from its module's imports. Namespace prefixes
`D5.S3.Zeros.Convolution` and private compiler mangling are omitted in the
labels. The worker-owned `attempt-2/semantic-receipt.json` retains the full
names, statement identities, and axiom sets.

| Public theorem | #print axioms |
| --- | --- |
| `GribinskiDegreeThree.convolution_coefficients` | `[propext, Classical.choice, Quot.sound]` |
| `GribinskiDegreeThree.definition_consistency` | `[propext, Classical.choice, Quot.sound]` |
| `GribinskiDegreeThree.m3_discriminant_nonneg` | `[propext, Classical.choice, Quot.sound]` |
| `GribinskiDegreeThree.m3_explicit_coefficients` | `[propext, Classical.choice, Quot.sound]` |
| `GribinskiDegreeThree.m3_nonnegative_coefficients` | `[propext, Classical.choice, Quot.sound]` |
| `GribinskiDegreeThree.m3_nonnegative_roots` | `[propext, Classical.choice, Quot.sound]` |
| `GribinskiDegreeThree.nonnegative_rootTriple_coordinates` | `[propext, Classical.choice, Quot.sound]` |
| `GribinskiDegreeThree.weight_pos` | `[propext, Classical.choice, Quot.sound]` |
| `GribinskiDegreeThreeDiscriminant.ordered_numerator_nonneg` | `[propext, Classical.choice, Quot.sound]` |

| Private theorem | #print axioms |
| --- | --- |
| `GribinskiDegreeThree.discriminant_numerator` | `[propext, Classical.choice, Quot.sound]` |
| `GribinskiDegreeThree.ordered_output_discriminant` | `[propext, Classical.choice, Quot.sound]` |
| `GribinskiDegreeThree.rootTriple_coefficients` | `[propext, Classical.choice, Quot.sound]` |
| `GribinskiDegreeThree.weight_values` | `[propext, Classical.choice, Quot.sound]` |
| `GribinskiDegreeThreeDiscriminant.coeff0_identity` | `[propext, Classical.choice, Quot.sound]` |
| `GribinskiDegreeThreeDiscriminant.coeff1_identity` | `[propext, Classical.choice, Quot.sound]` |
| `GribinskiDegreeThreeDiscriminant.coeff2_identity` | `[propext, Classical.choice, Quot.sound]` |
| `GribinskiDegreeThreeDiscriminant.coeff3_identity` | `[propext, Classical.choice, Quot.sound]` |
| `GribinskiDegreeThreeDiscriminant.numerator_expansion` | `[propext, Classical.choice, Quot.sound]` |
| `GribinskiDegreeThreeDiscriminant.ordered_coeff0_nonneg` | `[propext, Classical.choice, Quot.sound]` |
| `GribinskiDegreeThreeDiscriminant.ordered_coeff1_nonneg` | `[propext, Classical.choice, Quot.sound]` |
| `GribinskiDegreeThreeDiscriminant.ordered_coeff2_nonneg` | `[propext, Classical.choice, Quot.sound]` |
| `GribinskiDegreeThreeDiscriminant.ordered_coeff3_nonneg` | `[propext, Classical.choice, Quot.sound]` |
| `GribinskiDegreeThreeDiscriminant.sos0_nonneg` | `[propext, Classical.choice, Quot.sound]` |
| `GribinskiDegreeThreeDiscriminant.sos1_nonneg` | `[propext, Classical.choice, Quot.sound]` |
| `GribinskiDegreeThreeDiscriminant.sos2_nonneg` | `[propext, Classical.choice, Quot.sound]` |
| `GribinskiDegreeThreeDiscriminant.sos3_nonneg` | `[propext, Classical.choice, Quot.sound]` |

Final source checks: `git diff --check d625f554ae` exited 0.
`rg -n '\b(sorry|admit|axiom)\b|set_option (maxHeartbeats|maxRecDepth)'
D5/S3/Zeros/Convolution/GribinskiDegreeThree.lean
D5/S3/Zeros/Convolution/GribinskiDegreeThreeDiscriminant.lean` returned
0 matching lines, EXIT=1. This lexical result only corroborates the
kernel and semantic-report observations; it does not replace them.

The maximum `/usr/bin/time -l make lean` RSS across this attempt is
7801700352 bytes (certificate build, 64.18 seconds, EXIT=0). The last
`make lean` used 3097346048 bytes (19.71 seconds, EXIT=0). No budget
options, mathematical constants, or toolchain pins were changed.
The successful proof uses the planned four parameter coefficients and
separate identity/sign declarations; there is no remaining Lean goal.

Changed paths relative to the inherited `d625f554ae` checkpoint:

- `D5/S3/Zeros/Convolution/GribinskiDegreeThree.lean`
- `D5/S3/Zeros/Convolution/GribinskiDegreeThreeDiscriminant.lean`
- `docs/reports/convolution/gribinski-m3-0909.md`

`make gate` was not run, and no gate, CI, or admission approval is claimed.
This is the requested unfrozen branch delivery of Steps 4--5. The earlier
Step 3 bind-only assessment remains in force; the new certificate supplies
the proposed escape-witness basis for the combined content delivery.
independent_review: ASSUMED-UNVERIFIED. Literature completeness, priority,
and general-m Conjecture 3.13 remain explicitly unclaimed.

## Scribe Mirror Completion (2026-09-09)

Producer: one Codex implementation worker in the enclosing `consensus-rnd:sshx`
attempt; no additional skill or review seats invoked. All observations below
are this worker's readings, not independent review or orchestrator revalidation.
Initial HEAD: `edcaa0364b401e2a13a4e28bb7bd51ff1dbb5c07`; clean worktree.
This stage changes narrative sources, emitted projections, and this report only.

### Step 0: Gate and Capacity Source Read

`gate_found`: **SL-004, Mirror completeness**. Registration is at
`tools/StrataLint.Engine/Rules/RepositoryRules.cs:62`; its default effect is
Block and lifecycle Active (`:201`, `:212`). The evaluator calls
`ValidateMirror` at `Rules/RepositoryRules.Structure.cs:337`; the actual
missing-file predicate and finding are at `Rules/RepositoryRules.Helpers.cs:128`
and `:131`: `missing mirror <path>`. These `Rules/` paths are under
`tools/StrataLint.Engine/`. The rule is awakened by changed Lean/Blueprint
paths (`Rules/Scoping/RepositoryRules.Affected.cs:23`), and a changed formal
source selects its pair (`Rules/RepositoryRules.Helpers.cs:86`). Both committed
Lean headers name their own `D5/B/...` mirrors without waivers. GID conversion
maps those addresses to `Blueprint/D5/.../<module>.md`
(`tools/StrataLint.Engine/Coordinates/Gid.cs:192`). Thus the two missing `.md`
files satisfy the blocking predicate even though the modules are unfrozen.
This is source-based confirmation; `make gate` was not run.

Search receipt: `git grep -n -P '\bMirror completeness\b|\bValidateMirror\b|\bMirrorPairAffected\b|\bMirrorsAffected\b' -- tools/StrataLint.Engine`
returned 7 matching lines, EXIT=0; the registration is a positive word-boundary
control. `Meta/FILEMAP.toml:90` identifies `.md` as ScribeEmitter projections;
`:100` identifies `.scribe.cs` as ScribeCompiler-verified source data.

Capacity source: `RepositoryRules.Structure.cs:68` sets `DirectoryFileLimit=48`;
`:109` excludes Blueprint `.md`, and `:117` groups the remaining paths by their
immediate parent. After `git fetch origin dev` (EXIT=0), dev was
`96e7e6d8fea1c2e3a1ec17f56fcc411f671b674c`. Direct-child `git ls-tree -r --name-only`
counts for D5/Blueprint Convolution respectively: dev raw **16/32**, capacity
**16/16**; initial HEAD raw **18/32**, capacity **18/16**. Planned final raw
**18/36**, capacity **18/18**; actual counts will be repeated before pushes.

The m=2 source was read from `origin/dev`. Its theorem nodes use
`WithoutFormula`; the brief's cited `DescribeMigrationTests.cs:123-130` does
not exist in this checkout (the file has 67 lines). Those are not copied as
current requirements: all new theorem nodes will use `FromAuthor` as explicitly
required by this task. No mathematical, budget, or Digestion edit is authorized.

### Mirror A

Step 0 checkpoint `54d8ef5541` was pushed. The new main-module Scribe source
follows `GribinskiDegreeTwo.scribe.cs` for namespace, Prefix and Describe shape;
typed formulas use the existing FormulaDsl pattern from WeakQlpDifferentiation.
Its 17 nodes cover all 9 public definitions and 8 public theorems from the
committed Lean source at `edcaa0364b`. Every theorem has `FromAuthor`; every
body states all parameter types, assumptions and top-level conjuncts. The
coefficient theorem retains all four equalities, and each existential theorem
retains three nonnegativity conditions plus the polynomial equality.
The retained raw Lean report confirms these 17 declarations are included.
Private names are excluded separately: `include_in_statement=true` alone does
not imply public visibility in that report. Compilation/emit remains pending
until both mirrors have been committed, as required by the task sequence.
Before the A push, fetch EXIT=0 at dev `fe073d57308689f0d309d54d7d6fa7dbb8298484`;
index and dev/index path-union counts are raw **18/33**, capacity **18/17**.
`git diff --cached --check`: EXIT=0.

### Mirror B

Mirror A commit `5a60cb2429` was pushed. The discriminant mirror has exactly
two nodes: public `numerator` (definition, WithoutFormula) and public
`ordered_numerator_nonneg` (theorem, FromAuthor). The latter retains all seven
real binders, seven nonnegativity hypotheses, six local coefficient definitions,
and the complete numerator inequality from the committed Lean statement.
The formula expands the six local definitions. Private SOS and coefficient
declarations have no Describe nodes, even when included in the raw report.
Before the B push, fetch EXIT=0 at dev `fe073d57308689f0d309d54d7d6fa7dbb8298484`;
index and dev/index path-union counts are raw **18/34**, capacity **18/18**.
`git diff --cached --check`: EXIT=0; no `.lean` or Digestion path changed.

### Emit Boundary Correction

Mirror B commit `90c69725bc` was pushed. First `make emit`: EXIT=2,
29.60 real seconds (`emit.log` in the mirror attempt directory). C# compiled;
Scribe rejected `convolution-coefficients` because `Cdot` immediately followed
by identifier `b` would emit invalid LaTeX `\cdotb`. No tracked output changed.
The correction inserts explicit FormulaDsl spaces between control words and
following identifiers, including the shared nonnegative-relation builders.
No mathematical formula or Lean source was changed by this correction.

### Step 3: Emitted Projections and Echo Table

Correction commit `48bf865713` was pushed after fetch/recount: dev remained
`fe073d5730`, raw **18/34**, capacity **18/18**. Second `make emit`: EXIT=0,
64.92 real seconds (`emit-2.log`). Both new `.md` files were generated by this
command and read back. All 19 public handles resolved with generated `std3`
annotations; those annotations do not claim frozen membership.

The full emitter also refreshed eight unrelated `Blueprint/D5/S3/Weil/ZetaBridge/`
projections (wording changed from "theory volume" to "source analysis"). The tree
was clean before emit. Its exact unrelated diff is retained in the worker-owned
`emit-unrelated.diff`; these eight emitter-created changes were restored to HEAD
without editing their Scribe sources. Only the two requested projections enter
the emit commit. No Blueprint Markdown was hand-authored.

`echo_table`: A means `D5/S3/Zeros/Convolution/GribinskiDegreeThree`, B means
`D5/S3/Zeros/Convolution/GribinskiDegreeThreeDiscriminant`. Each declaration
below is `<module>.<name>`; line numbers refer to its `.lean` at `edcaa0364b`.
All rows were transcribed from committed source, with theorems read through
`:= by`, and checked against the public included declarations of the report.

| Module / Describe ID | Lean declaration : line | FromAuthor |
| --- | --- | --- |
| A / elementary-coefficient | elementaryCoeff : 36 | no (definition) |
| A / weight | weight : 40 | no (definition) |
| A / normalized-coefficient | normalizedCoeff : 43 | no (definition) |
| A / coefficient-convolution | convolutionCoeff : 47 | no (definition) |
| A / polynomial-convolution | boxplus3 : 52 | no (definition) |
| A / root-triple | rootTriple : 57 | no (definition) |
| A / definition-consistency | definition_consistency : 60 | yes |
| A / kappa | kappa : 65 | no (definition) |
| A / rho | rho : 68 | no (definition) |
| A / convolution-coefficients | convolution_coefficients : 86 | yes |
| A / explicit-cubic | m3_explicit_coefficients : 110 | yes |
| A / positive-weights | weight_pos : 123 | yes |
| A / nonnegative-coefficients | m3_nonnegative_coefficients : 130 | yes |
| A / discriminant | discriminant : 149 | no (definition) |
| A / ordered-gap-coordinates | nonnegative_rootTriple_coordinates : 157 | yes |
| A / nonnegative-discriminant | m3_discriminant_nonneg : 226 | yes |
| A / nonnegative-roots | m3_nonnegative_roots : 237 | yes |
| B / discriminant-numerator | numerator : 26 | no (definition) |
| B / ordered-numerator-nonnegative | ordered_numerator_nonneg : 360 | yes |

Before the emit push, fetch EXIT=0 at dev `fe073d57308689f0d309d54d7d6fa7dbb8298484`;
index and dev/index path-union counts are raw **18/36**, capacity **18/18**.
`git diff --cached --check`: EXIT=0.

### Step 4: Lean Build

Emit commit `f3204fbd04` was pushed. `/usr/bin/time -l make lean`: EXIT=0,
**8.73 real seconds**, 12681 jobs, maximum RSS 1174421504 bytes (`lean.log`).
Cache receipt: present, method=none, project and Mathlib both warm. Both task
modules were replayed from the private cache; this is an incremental build
measurement, not a fresh proof benchmark. The four already recorded unused
variable warnings in the discriminant module remain. No Lean source was edited.
Before this verification checkpoint's push, fetch EXIT=0 at dev `fe073d5730`;
index and dev/index path-union counts remain raw **18/36**, capacity **18/18**.

### Semantic Report and Final Conclusion

Lean-build checkpoint `4347266f60` was pushed. `make lean-report`: EXIT=0,
10.53 real seconds (`lean-report.log`), mode=cached. Its input address remains
`sha256:a20ab3bd7c3261e58c6f85f9c399e3b5a3f61e6b30d117bbc35fa45374ae880d`;
report SHA-256 remains `20b925ef0ef86b656f60079b914364b66292344a31b3ab47ea941c67d6735b09`.
The public included sets contain 17/2 declarations, including 8/1 theorems,
with no axioms outside `Classical.choice`, `Quot.sound`, `propext`.
`public-declarations.json` and `emit-targets.json` retain the producer records
in the mirror attempt directory; no fresh proof reconstruction is claimed.

`gate_found`: SL-004 / Mirror completeness,
`tools/StrataLint.Engine/Rules/RepositoryRules.cs:62`, missing-file finding at
`tools/StrataLint.Engine/Rules/RepositoryRules.Helpers.cs:131` (details above).
`exit_codes`: make lean=0; make lean-report=0; make emit=0 after the recorded
initial emit=2. The successful emit did not need any Lean or budget edit.

`directory_counts`, after the final pre-push `git fetch origin dev` (EXIT=0)
at `83e5ffe53fcaeb3770f3d50658aa38cc8b011bda`: dev raw **16/32**, capacity
**16/16**; candidate index and dev/index path union raw **18/36**, capacity
**18/18**. Capacity headroom is 30 counted files in each directory (limit 48).
`directory-counts.json` retains the direct-child counting receipt. At checkpoint
`4347266f60`, `git merge-tree --write-tree origin/dev HEAD` returned EXIT=0,
tree `cb135032ef013987f331a01ce79c420ea98085e9`, with no conflicts.

`changed_paths` relative to this worker's inherited `edcaa0364b`:

- `Blueprint/D5/S3/Zeros/Convolution/GribinskiDegreeThree.scribe.cs`
- `Blueprint/D5/S3/Zeros/Convolution/GribinskiDegreeThreeDiscriminant.scribe.cs`
- `Blueprint/D5/S3/Zeros/Convolution/GribinskiDegreeThree.md`
- `Blueprint/D5/S3/Zeros/Convolution/GribinskiDegreeThreeDiscriminant.md`
- `docs/reports/convolution/gribinski-m3-0909.md`

`pushed.commits` completed before this final report commit: `54d8ef5541` (gate
readings), `5a60cb2429` (mirror A), `90c69725bc` (mirror B), `48bf865713`
(formula token boundaries), `f3204fbd04` (emit), `4347266f60` (Lean reading).
The worker-owned result envelope records full SHAs including this report's
commit after its push succeeds. `echo_table` is the complete 19-row table above.

`assumed_unverified`: no independent review seats or remote required-CI checks
were run in this stage. Formula fidelity was checked by this worker against
committed Lean statements; typed emission is not an independent semantic proof
of the narrative. No admission/CI-green claim, general-m result, or priority
claim is made. The inherited `.lean` files, all budget constants, and
`Meta/Digestion/**` are unchanged by this worker.

Explicitly not performed: **make deposit; make cover; freezing; opening a PR;
make gate**. The requested mirror preparation and local verification are
complete; the branch is ready to present for PR review under these limits.
