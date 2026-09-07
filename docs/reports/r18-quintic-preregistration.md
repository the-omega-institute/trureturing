# r18 quintic preregistration

Date: 2026-09-07. Worktree: `/private/tmp/wt-lineA`.
Branch: `lane/math/r18-quintic-0907`. Base: `22c63f8d3a`.
Tier: first, an explicitly numbered conjecture in a recent paper.
Provenance: one Codex implementation worker, no locally invoked skill or
independent review agents. The dispatch supplies the proposed coefficient
estimate and consumer; this worker independently checks the source and proof.

## Target and source check

The target is Conjecture 5.3 for degree five in Campbell, Morales and Perales,
*Even Hypergeometric Polynomials and Finite Free Commutators*,
arXiv:2502.00254v2, SIGMA 21 (2025), 108.
Canonical verified locator scope: v2 PDF, Notation 5.1 on printed page 19,
Conjecture 5.3 and Theorem 5.6 on printed page 20, Remark 5.7 on page 21.
The source defines `Sym(p) boxtimes_n Sym(q) boxtimes_n z_n`.
Theorem 5.6 requires an extra factorization and is not the full conjecture.
The dispatch's Gribinski attribution is not the authorship of this conjecture.
DOI `10.3842/SIGMA.2025.108` was checked against the PDF title page and the
Crossref works API. This report is not a Library note.

Independent literature recheck: arXiv exact-phrase search returned the source;
the broader finite-free/commutator search also returned Campbell's
arXiv:2209.00523 and a 2026 Hurwitz-series paper. OpenAlex exact-phrase search
returned the source's two records and arXiv:2604.13819 and arXiv:2606.15003.
Downloaded and searched those texts plus arXiv:2609.01555. The 2026 texts only
mention the commutator paper in their references; no proof of the target was
found in this searched scope. Source v2 remains the latest returned version.
This is not a claim of exhaustive literature absence. Google returned a script
interstitial, DuckDuckGo a challenge, and Bing unrelated results; these were
not counted as successful literature searches. PDF extraction introduced NUL
bytes, so the final text searches explicitly used `rg -a`.

## Bind-only attempt, before new content

Searched D5, pinned Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`,
GitHub Lean sources, and PerAlexandersson/RealRooted. No target or sharp bound
was found in these searches. Positive controls found
`centered_quartic_invariant_bounds`, `prod_X_sub_C_coeff_card_pred`, and
`finiteSymbolTheorem`, respectively. All commands and exit codes belong in
the worker result's readings, including unsuccessful commands.

The first attempted proof path is instantiation of the frozen quartic bound
at `(3*u/5, 2*v/5, w/5)`, followed solely by algebraic normalization.
It yields `u <= 0`, `-3*u^2/20 <= w`, and `w <= 9*u^2/20`.
These inequalities alone do not imply the proposed sharper upper bound:
`u = -1, w = 9/20` satisfies them and violates `w <= 4*u^2/15`.
A Lean scratch probe will check this normalization and counterassignment.
No successful bind-only proof has been found. If one is found, stop and
report bind-only without submitting a new module.

## Escape witness, registered before implementation

For every monic, centered quintic `p = X^5 + u*X^3 + v*X^2 + w*X + t`
having five real roots counted with multiplicity, prove exactly
`w <= (4/15)*u^2`.
Equivalently, for five real numbers with sum zero,
`sum r_i^4 >= (7/30)*(sum r_i^2)^2`.
No weakening of the constant is permitted. The calibration roots are
`(2,2,2,-3,-3)`, with `u=-15` and `w=60`.
Status at registration: ASSUMED-UNVERIFIED, awaiting a kernel proof.

Planned live dependency direction:
`quintic_real_rooted -> centered_factorization -> sharp coefficient bound`.
The lower coefficient bound must consume
`D5/S3/Zeros/Convolution/FiniteFreeCommutatorDegreeFour.centered_quartic_invariant_bounds`
after multiplicity-aware Rolle. Its frozen module statement identity is
`sha256:e4f15f5c0461a866887270b3ea9714ad3cb9c7bf4a40afe95cc84c3488442c13`.
The full direct frozen dependency list is to be reported per public theorem.
Expected admission basis: escape-witness, only if the exact bound is proved
and used on the conclusion's live proof path.

## Acceptance and stopping conditions

Success requires the exact bound, definition-derived degree-five convolution
coefficients, the discriminant bound `25*u^2*U^2/324`, nonnegative quadratic
factors, all zero and repeated-root cases, and translation to arbitrary monic
quintics. Build only through `make lean` or `make lean-report`; retain actual
`#print axioms` output. Never edit a frozen module or the frozen state surface.
If a literature proof is found, stop immediately and report its source.
If the sharp estimate cannot be closed, report the precise unproved obligation
and do not submit a weaker result as this target.
