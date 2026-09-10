# A395842 implementation record

## Provenance and scope

One Codex implementation worker using the `lean4` skill, with no delegated workers
or independent review in this attempt. The numerical and literature readings in
the task brief are supplied by the orchestrator and triage worker; they are not
reported as this worker's own measurements.

Repository: https://github.com/the-omega-institute/trureturing
Branch: `lane/math/a395842`.
Initial base: `6af98a19b1fd4f76f1bc1bf92b61593a0c167a09` (`origin/dev`).
Tier: 第一档 (recent OEIS conjecture).

Target: for the uniquely specified integer power series with g₀ = 0,
g₁ = g₂ = 1 and coeff n (G iterated n) = coeff n (G iterated (n−1))
for n > 2, prove 2 divides the diagonal coefficient for every n ≥ 2.
Neither the series nor the diagonal sequence may encode the parity conclusion.
No extension to the parity conjecture for A177775 is in scope.

## Preregistration

Proposed bridge, still ASSUMED-UNVERIFIED: identify G modulo 2 with
H = Σᵣ x^(2^r), prove the iterate coefficient formula
[x^(2^r)] H iterated m = choose(m+r−1,r) modulo 2, and use binary
binomial arithmetic plus the additive support to discharge the diagonal rule
and the diagonal parity. The nontrivial candidate witness is the connection
between the implicit diagonal constraints and this characteristic-two series.
Before implementation, search D5, pinned Mathlib, and the external Lean/literature
ecosystem, including every public declaration of the two specified iterate modules.

No theory volume or atom will be created. Any justified freeze uses the existing
uncovered-deposit / ledger-align --add path. Stop on a published proof of the same
diagonal conjecture, on a route depending only on the unproved A177775 claim,
or on an already proved bridge leaving only binding and index rewriting.

## Initial instruction reading

Read the complete CLAUDE.md, agents/CONTEXT.md and lean4/SKILL.md.
User-required persistent commits and the repository make/cache/gate protocol
override the skill-only default of a single pass without commits.
The task's implementation completion condition is a proved target with a PR;
it does not authorize claiming that an unmerged PR has landed on dev.

## Current result

The full parity theorem and `make lean` pass. Report production, Scribe checks,
freeze and PR remain in progress; no freeze or landed PR is claimed yet.

Historical proof checkpoints (their pending statements refer to that checkpoint):

First Lean unit checked: the degree-n residual changes by exactly the change
in g_n, and the diagonal constraints give uniqueness over any commutative ring.
`lake env lean D5/S1/Recurrence/Parity/DiagonalIterateEven.lean` (warm tree)
EXIT=0; `diagonal_unique` axiom closure is propext, Classical.choice, Quot.sound.
This is a general symbolic lemma, not a finite numerical check. It is currently
private and unfrozen, on the planned live path to the final series construction.

Second Lean unit checked: construct the integer series by successively subtracting
the residual times X^n, prove the coefficient limit satisfies all normalization
and diagonal constraints, and prove uniqueness. `generatingSeries` and `a` have
no parity condition in their definitions. The private semantic echo `a 2 = 2`
also checks. Warm file check EXIT=0; all three printed axiom closures contain
only propext, Classical.choice, Quot.sound. The first run caught a definitional
unfolding mismatch in extend_correct; unfolding extend in the goal repaired it.
This proves existence/uniqueness, not yet the parity conjecture.

Third Lean unit checked: H is Mathlib's compositional inverse of X+X² over
ZMod 2; prove H+H²=X and, for every r,
H^∘(2^r)+(H^∘(2^r))^(2^(2^r))=X. `H_dyadic_gap` and the degree-gap coefficient
consequence pass the warm file check (EXIT=0, three standard axioms only).
The first run exposed substitution folding, a missing PowerSeries CharP instance,
and a sign in the doubling calculation; all were corrected before this checkpoint.
No binomial formula or unproved A177775 assertion was used.

Fourth Lean unit checked: non-dyadic coefficients of every H iterate vanish by
strong induction on degree and induction on iteration count; the dyadic gap
handles powers of two. H satisfies the implicit diagonal constraints. Mapping
the integer solution into ZMod 2 and applying diagonal uniqueness identifies it
with H. `hanna_conjecture (n) (hn : 2 ≤ n) : 2 ∣ a n` passes the warm file check,
EXIT=0, with only propext, Classical.choice, Quot.sound. All printed public
theorem closures are clean. Full repository gates and PR are still pending.

The canonical https://oeis.org/A395842 page was also opened and read in full;
its DATA and conjectural comment agree with the official text response.
The additional Loogle `"PowerSeries", "iterate"` query returned 15 declarations:
analytic derivative iterations and Frobenius expansion, no compositional
diagonal rule. Exact locator receipts are in locator-receipts.json.
The Library note includes its verified locator section and no DOI is asserted.

Capacity detail: the mirrored Blueprint bucket has 52 physical files but only
26 counted sources. RepositoryRules.Structure.IsCapacityExcluded explicitly
excludes its generated .md projections. Thus the new source occupies slot 27.
The same canonical capacity source sets the soft/hard file-line limits to
800/1000 (the older spec A5 prose still says 400); no capacity mechanism changed.

## Search receipts and semantic correction

Local searches used `rg` over D5 for A395842, A177775, diagonal iteration,
substitution coefficients and dyadic support. Read every public declaration of
CompositionalIterateCongruence and ShiftedIterateFixedPointCongruence (whole files).
The former's public surface is iterate, step, fixed_unique, approximation, a,
generatingSeries, generating_equation, mobius, mobius_iterate, mod_ten_fixed,
coefficient_congruence. The latter's is a, generatingSeries, generating_equation,
generating_unique, mod_identity, shift_iterate_mod, hanna_conjecture_five/six.
Reuse `iterate` directly. No public perturbation or general congruence lemma is
exported by these files. Read IterateProductNineModThree in full: its useful
`iterate_top` and substitution perturbation lemmas are private; its public
lift_mod_nine concerns a different mod-nine product. Such private proofs can
guide local proofs but are not callable public frozen dependencies.

Pinned Mathlib searches: PowerSeries/Substitution (coeff_subst', map_subst,
subst_comp_subst_apply, substInvOfIsUnit, both inverse equations), Expand
(Frobenius expansion), Nat/Choose/Lucas (digit congruences). These give operations,
not the implicit diagonal bridge. Public Loogle query `"PowerSeries", "subst"`
returned Mathlib substitution declarations; online version is not the pin, so
the pin is checked locally before using any declaration. GitHub repository
searches `Lean power series composition` and `A395842` returned total_count=0;
these limited repository-name/metadata searches do not rule out hidden proofs.
arXiv number query returned totalResults=0. Google phrase/number requests returned
HTTP 200 redirect/interstitial pages, not search results; they provide no negative
literature evidence. URLs, response sizes and SHA-256 are in search-receipts.json.

Actually opened both official OEIS text responses in full. Their conjectural
comments agree with the supplied triage assessment. No proof was found in these
opened sources. This is not an exhaustive absence claim.

**Correction to supplied numerical reading:** official A395842 DATA begins
1,2,−6,66; the task brief says a(2)=4. The stated normalization gives
[x²](G∘G)=g₁g₂+g₂g₁²=2. The target remains the same, since both 2 and 4 are even.
The brief's claim of all DATA equality therefore cannot include its reported
a(2)=4. No larger enumeration is planned to replace a proof.

## Preregistration revision 2 (before proof experiments)

Retain the implicit uniqueness bridge; replace the proposed binomial/Lucas
implementation with this candidate equivalent mechanism, still unverified:
let P=X+X² over ZMod 2 and H be its compositional inverse (via pinned Mathlib).
Prove P iterated 2^r = X+X^(2^(2^r)); transport the inverse relation to obtain
H iterated 2^r + (H iterated 2^r)^(2^(2^r))=X. This gives vanishing coefficients
in the required degree interval. The relation H^∘(m+1)+(H^∘(m+1))²=H^∘m
gives support only at powers of two by induction on degree. Together they imply
the diagonal rule and parity for H. The proposed escape witness is this
degree-gap identity on the live path from implicit uniqueness to the final parity.
No existing proved H/diagonal bridge was found, so the high-bind stop does not apply.

## Build environment

Lean 4.33.0 and Mathlib db584cd6d46c92f209a44c0f1c829460d327499d match the task.
`make lean-cache-ensure` EXIT=0: status=seeded, method=clonefile,
donor=/Users/chronoai/trureturing, clonefile_attempts=1, stamp_miss=null,
mathlib_olean_state=warm, project_olean_state=warm, mathlib_missing_olean_files=0.
No cold bare lake command was run. Parity target bucket currently has 26 files
(`find D5/S1/Recurrence/Parity -type f | wc -l`), below 48. The spec A5.1 utility
grammar and registered Recurrence domain were checked.

## Unclaimed

No claim of an exhaustive literature search, a resolution of A177775,
an independent review, a freeze, or a landed PR has been made yet.
Unopened external pages are ASSUMED-UNVERIFIED.

## Repository gate receipts

`make lean`: EXIT=0, 379.806 seconds on this macOS ARM worktree; final output
`Build completed successfully (12896 jobs)`. The new module took 5.7 seconds.
LEAN_CACHE: status=present, method=none, stamp_miss=null, both project and Mathlib
warm, no missing Mathlib oleans, archive not attempted. The initial clonefile
seed is recorded above. Full structured receipt: build-receipts.json; raw log
is the attempt directory's make-lean.log. These local timings are not CI timings.

## Elaborated dependency audit

A warm-tree Lean metaprogram traversed each public theorem's elaborated type
and value, descending into local declarations and stopping at other D5 constants.
EXIT=0 after correcting two audit-only API/syntax errors (`prefix` is reserved;
name conversion uses String.toName). The complete source and output are in
dependency-audit.json. This audit verifies constant reachability, not semantic
necessity or an automatic proof-shape classification.

All three public theorem closures reach the imported `iterate` definition and
its generated equation `iterate.eq_2`, with no other external D5 constant
boundary. The first two reach `residual_top`; hanna_conjecture reaches
`H_dyadic_gap`. The live mathematical paths and semantic four-part assessment
are recorded below once the canonical declaration pins are available.

## Per-theorem admission assessment

The assessed module basis is `admission_basis: escape-witness`. These semantic
classifications are worker assessments under CLAUDE 3.2, not machine verdicts.
All public theorem statements are unbounded symbolic assertions; `utility: none`
is appropriate because none is one of the four computational content classes.
The finite positive echo `initial_echo` is private and is not independently frozen.

| Public theorem | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| generating_equation | content | residual_top, used through extend_correct | escape-witness |
| generating_unique | content | residual_top, used through diagonal_unique | escape-witness |
| hanna_conjecture | content | H_dyadic_gap | escape-witness |

For `generating_equation`, all four conditions hold as follows.
(i) The elaborated audit contains residual_top and extend_correct.
(ii) The imported iterate definition and its recursion equation do not supply
the response of the degree-n diagonal residual to an arbitrary coefficient
perturbation; finite substitution sums and induction on the iterate establish it.
(iii) This perturbation identity compares arbitrary normalized series over a
commutative ring and is neither the constructed limit's specification nor its
definition. (iv) residual_top → extend_correct → approximation_correct →
limit_spec.2.2.2 → generating_equation's final conjunct is a live path. The
normalization projections alone cannot yield the diagonal constraints.
The proof pattern follows private helpers in IterateProductNineModThree as
explicitly credited in the Lean source; no public frozen perturbation API was found.

For `generating_unique`, (i) the audit reaches residual_top through diagonal_unique.
(ii) Equality at the next coefficient is newly forced using the residual identity
and strong induction, and is not supplied by the imported iterate recursion.
(iii) A one-degree perturbation identity for arbitrary series is not definitionally
equivalent to uniqueness of the integer solution. (iv) diagonal_unique uses
residual_top to close every degree beyond the three prescribed coefficients;
this proof term survives reduction and is the value of generating_unique.
The constructed solution's limit_spec supplies the second solution's assumptions.

For `hanna_conjecture`, (i) H_dyadic_gap occurs in the elaborated closure.
(ii) Neither Mathlib's inverse existence nor the imported iterate definition gives
the doubly exponential degree gap. Its proof inducts on r using composition and
Frobenius in characteristic two. (iii) The identity
`iterate H (2^r) + (iterate H (2^r))^(2^(2^r)) = X` is about an auxiliary inverse
series, not the definition of G, a, or integer diagonal evenness.
(iv) H_dyadic_gap → H_dyadic_coeff → H_diagonal / H_previous_diagonal →
H_residual → mod_two_identity → hanna_conjecture is live; H_diagonal also
directly supplies the final zero coefficient. H_support handles the complementary
non-dyadic degrees. The inverse and uniqueness facts alone give neither the
needed H diagonal constraint nor its vanishing diagonal.

The two public definitions are mathematical interfaces for the constructed
series and diagonal coefficients. They assert no parity fact. No unrelated
public finite instances or extra A177775 characterization were added.

Before freezing, fetched origin/dev and searched its D5, Blueprint, Library and
reports for A395842 and H_dyadic_gap. At
6af98a19b1fd4f76f1bc1bf92b61593a0c167a09, only the supplied triage note matched;
there was no D5 implementation. `git merge-tree --write-tree HEAD origin/dev`
returned EXIT=0. The search is bounded to these repository paths and that SHA.
