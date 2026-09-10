# Section cover batch, 2026-09-09

## Provenance and scope

- Skill context: no skill invoked; the assigned implementation worker reads the
  tracked probe brief directly. The surrounding runner is supplied by the user.
- Carrier and roles: one Codex implementation worker performs the clause audit,
  writes this report, and invokes the canonical cover and PR commands. There are
  zero independent review seats in this worker's delivery.
- Mixing: sequential audit and self-check. The earlier screening report is an
  input, not an independent approval of these new coverage edges. The user's
  five PIN_MATCH readings are supplied evidence, not worker measurements.

Baseline HEAD and the initially resolved origin/dev are both
`1bb54f920527c303ebaec4e5388d48fcbee0df04`.
Branch: `lane/math/section-cover-batch-0909`.
The complete tracked probe brief, CLAUDE.md, agents/CONTEXT.md, and the screening
report have been read before content changes. The screening report is read from
commit `d43088b76be65982a2fc8270da3c2137ebbea94f`, path
`docs/reports/digestion/section-cover-screen-0909.md` (659 lines).
Its history was inspected with
`git log --oneline origin/dev..origin/lane/math/section-cover-screen-0909`.
The existing untracked `candidates.json` is a supplied input, outside this diff.
The continuation resumed from the supplied conversation summary, existing
commits and command logs; it is part of the same implementation stream, not an
independent review.

## Preregistered decision rule

Read each full atom with `make show-atom ATOM_ID=<64-character basename>`.
Read the nominated frozen declaration through its `:= by`, including definitions
and source context needed to fix the meaning of its symbols. Each boxed clause
and adjacent assertion receives `verbatim`, `equivalent`, or `not-covered`, with
explicit binders, hypotheses, conclusions, endpoint and quantifier checks.
Any unmatched A-group assertion means `verdict: partial` and no cover for that
atom. Only a full match permits a canonical `make cover` call. A successful
writer exit is not evidence of mathematical fidelity.

A group: audit and, only when all clauses match, cover G2, the 5040 open price
interval, and the ordered positive quadruple classification. B group: write
transport dossiers for U1 and dynamics descent; no cover call for either B atom,
regardless of the eventual recommendation. No Lean edits, deposits, or freezes.
Commit and push this report progressively, including after every atom. Open a
PR using `make pr-open`, without `AUTO_MERGE`; this delivery does not claim merge.

## Initial atom inventory

All five paths were located with the user-specified full-basename `find` query.
All have source_id `quantum-rh` and initial directory `residual-open`.

| Group | Atom ID | Initial state | Result |
| --- | --- | --- | --- |
| A1 | `66fd622e5d54c25826af9d416db18df1d8eecf9c71288d80ff0460237e3e95d2` | residual-open | absorbed-closed; two edges |
| A2 | `088d882f6a10249e981da5d77bc3bb5e53e75a5ee02313bdd7c879cb21e22413` | residual-open | absorbed-closed; one edge |
| A3 | `5f5912050d91b5f8998e6799d12c40e766fa4d65798ff890b506a56c3bc0ed3c` | residual-open | absorbed-closed; one edge |
| B1 | `c352d304105e02cbbcb0607e31a1e217adb85d4b344ba0d75c23ba4420dbf0e1` | residual-open | residual-open; dossier only; needs a Lean bridge |
| B2 | `7b2657006891568aa395dfd9fa14bde9d9d23d2ade0c449b00f7cdf5c616baec` | residual-open | residual-open; dossier only; needs a Lean bridge |

## A1: G2 discriminant

Atom: `66fd622e5d54c25826af9d416db18df1d8eecf9c71288d80ff0460237e3e95d2`.
`make show-atom` returned 0, the complete raw and normalized body, and empty
coverage. The body defines P=a+b, Q=c+d, and D as the discriminant of G1's
quadratic. Its single box contains an equality followed by a non-strict bound;
the adjoining sentence supplies the repeated-input equality case.

Frozen module: `D5/S3/Zeros/Convolution/GribinskiDegreeTwo`.
The actually read state file is
`Golden/Frozen/state/D5/S3/Zeros/Convolution/GribinskiDegreeTwo.lean.json`;
its module pin is
`sha256:184c298cb6b3a6b32640e84511f41eede52d8d0d29ae2b24a68f14ef5722487e`.
The two intended declaration GIDs are:

- `D5/S3/Zeros/Convolution/GribinskiDegreeTwo.g2_discriminant_bound`
- `D5/S3/Zeros/Convolution/GribinskiDegreeTwo.discriminant_eq_output`

Read with `git show origin/dev:D5/S3/Zeros/Convolution/GribinskiDegreeTwo.lean`:
definitions and both complete signatures through `:= by`, at lines 145-168.
All five binders are `Real`. `g2_discriminant_bound` has no hypotheses;
`discriminant_eq_output` has exactly `alpha != -1` and `alpha != -2`.
The latter are source restrictions, not new assumptions:
`QUANTUM-RH.md:60801-60821` excludes those two values for the entire G1-G4
addendum. This audit directly read that context and the appended correction at
`QUANTUM-RH.md:61194-61232`, which prescribes the product prefactor. `weight`,
`convolutionCoeff`, `boxplus`, `rootPair`, and `kappa` use that corrected meaning.

| Source clause | Lean binders | Lean hypotheses / conclusion | Label |
| --- | --- | --- | --- |
| For all a,b,c,d >= 0; real alpha != -1,-2 from the shared setting | `alpha a b c d : Real` | G2 is valid on all reals and may be specialized to nonnegative roots; the output bridge has precisely the two source exclusions | equivalent |
| P=a+b, Q=c+d, D is the discriminant of G1's output | same five reals | `discriminant_eq_output`: D equals `discrim` of the actual `boxplus` coefficients 2,1,0; `rootPair` is `(X-C a)*(X-C b)` | equivalent |
| Box: D=(P+Q)^2-4ab-4cd-4*kappa(alpha)*P*Q | same five reals | `g2_discriminant_bound ... .1`, expanding P,Q and reassociating addition; `kappa alpha=(alpha+1)/(2*(alpha+2))` | equivalent |
| Box: D >= 2*P*Q*(1-2*kappa(alpha)) | same five reals | `.2.1`: `2*(a+b)*(c+d)*(1-2*kappa alpha) <= discriminant alpha a b c d` | verbatim |
| Adjoining sentence: when a=b AND c=d, equality holds | same five reals | `.2.2`: `a=b -> c=d -> D=2*(a+b)*(c+d)*(1-2*kappa alpha)` | verbatim |

Quantifier and endpoint audit: universal parameters, no existential witness;
non-strict root inequalities include zero; the discriminant bound is non-strict;
alpha is not silently restricted to alpha>-1. The equality sentence is a
sufficient condition, not an iff. Both alpha singular endpoints remain excluded.
There is no extra hypothesis after specializing the stronger scalar theorem.
No assertion of the former ratio-prefactor definition is covered.

Fidelity verdict: full match. Proposed use `proof_shape: bind-only`,
`escape_witness: null`,
`admission_basis: not-applicable(cover of existing frozen declarations)`.
Direct frozen dependencies are the two GIDs above with the recorded module pin;
this does not audit or reclassify the original frozen proof's dependency closure.

Search receipt: `git grep -n -P
'\btheorem\s+(g1_explicit_coefficients|g2_discriminant_bound|discriminant_eq_output)\b'
origin/dev -- D5/S3/Zeros/Convolution/GribinskiDegreeTwo.lean` found exactly three
lines, one per declaration. `g1_explicit_coefficients` is the positive control
with the same word-boundary, whitespace and alternation features.
Negative control with the same regex features:
`git grep -n -P '\btheorem\s+(section_cover_absent_0909|section_cover_missing_0909)\b'
origin/dev -- D5/S3/Zeros/Convolution/GribinskiDegreeTwo.lean` found zero lines,
exit 1 (expected no-match, not a validation failure).

Writer receipt: `make cover-batch ATOMS=<attempt-1>/a1-cover.tsv
BASE=1bb54f920527c303ebaec4e5388d48fcbee0df04` returned 0 and `status=applied`.
The TSV has two rows for this one atom. The resulting directory is
`Meta/Digestion/backfill/quantum-rh/absorbed-closed/`; the old residual path is
absent. The emitted report changed zero blueprints, and `git diff --check`
returned 0. The only ledger delta is this atom's migration and its two edges.
Declaration pins written by the canonical writer (distinct from the module pin):

- `discriminant_eq_output`: `sha256:f1485302da7dad7c340240c52ed1003a06a757b6795d07e8bc9d605fde7e4a9f`
- `g2_discriminant_bound`: `sha256:0da02bd7a338b4c210dec5b5e2512019e7ea5d99f32295ff662fdfb7ed00e790`

The canonical Lean report used the existing warm cache and refreshed 32 baseline
additions (`changed=0 added=32 removed=0 recheck=32`), then produced report
`sha256:af574b21fd88feb264bfc954cbb4ae54eece0589735a3cc802ed51c919d17e16`.
These are report-production readings, not new Lean source changes by this worker.

## A2: 5040 open price interval

Atom: `088d882f6a10249e981da5d77bc3bb5e53e75a5ee02313bdd7c879cb21e22413`.
`make show-atom` returned 0 with the complete raw/normalized body and no initial
coverage. There are two boxes: the strict price interval (31), and `5040`, whose
adjoining predicate says it is the unique global maximizer over positive integers.

Frozen declaration GID:
`D5/S3/Arith/GoldenResource5040PriceInterval.golden_resource_5040_unique_maximum_of_price_interval`.
The actually read state file is
`Golden/Frozen/state/D5/S3/Arith/GoldenResource5040PriceInterval.lean.json`, pin
`sha256:5ff6c71eede645e4240967fc93b7f3e64324a924d1ed5ba9b002a637e96a3e69`.
`git show origin/dev:D5/S3/Arith/GoldenResource5040PriceInterval.lean` was read
through the nominated signature's `:= by` (lines 278-284). Its exact shape is
universal `{lambda : Real}`, the two strict price hypotheses, universal `{n : Nat}`,
`hn : 1 <= n`, and a conjunction of the maximum inequality and equality iff.
No further theorem parameters or RH assumption appear.

| Source clause | Lean binders | Lean hypotheses / conclusion | Label |
| --- | --- | --- | --- |
| Box (31), lower endpoint: log(12/11)/log(11) < lambda | `{lambda : Real}` | `hlower : Real.log (12 / 11) / Real.log 11 < lambda`; left endpoint excluded | verbatim |
| Box (31), upper endpoint: lambda < log(31/30)/log(2) | same lambda | `hupper : lambda < Real.log (31 / 30) / Real.log 2`; right endpoint excluded | verbatim |
| All positive integers N | `{n : Nat}` | `hn : 1 <= n`; exactly equivalent to `0 < n` in Nat, including 1 and excluding 0 | equivalent |
| Objective F_lambda(N)=log(sum over d dividing N of 1/d)-lambda*log(N) | `lambda : Real`, `n : Nat` | `goldenResourceObjective` at GoldenResourceOptimalInteger.lean:22 uses `Real.log (sum d in n.divisors, (d : Real)^(-1)) - lambda * Real.log n` | equivalent |
| Box `5040` with adjoining global-maximum predicate | arbitrary positive n at each admissible lambda | First conjunct: `goldenResourceObjective lambda n <= goldenResourceObjective lambda 5040` | verbatim |
| Same box and adjoining unique-maximum predicate | the same n and lambda, same three hypotheses | Second conjunct: `(goldenResourceObjective lambda n = goldenResourceObjective lambda 5040) <-> n = 5040` | verbatim |

The objective definition was read from origin/dev and compared with
`QUANTUM-RH.md:38236-38250`: reciprocal notation and the finite positive-divisor
index are the same. The surrounding source assumes lambda>0; this follows from
the positive lower threshold (both logarithms are positive), so it adds no
restriction to the Lean interval. Numerals 12/11 and 31/30 are real division
inside `Real.log`, not truncated Nat division. The maximizer comparison is
non-strict, while the price hypotheses are strict. Uniqueness is an actual iff,
not merely existence of a maximizing point. The domain is unbounded positive
Nat, not prime-only, smooth-only, or a finite tested range.

The unboxed decimal sentence explicitly says approximately. A double-precision
observation gave lower `0.036286562627101906` and upper `0.04730571477835682`;
rounding to eight decimal places yields the source's `0.03628656` and
`0.04730571`. These are not substituted as exact endpoints and are not claimed
to be kernel-certified numerical bounds.

Fidelity verdict: full match. Proposed use `proof_shape: bind-only`,
`escape_witness: null`,
`admission_basis: not-applicable(cover of an existing frozen declaration)`.
The direct frozen dependency is the declaration GID above, with its module pin.
Writer receipt: `make cover ATOM_ID=088d882f6a10249e981da5d77bc3bb5e53e75a5ee02313bdd7c879cb21e22413
GID=D5/S3/Arith/GoldenResource5040PriceInterval.golden_resource_5040_unique_maximum_of_price_interval
BASE=1bb54f920527c303ebaec4e5388d48fcbee0df04` returned 0, with
`ledger_changed=true`. The atom moved from `residual-open` to `absorbed-closed`,
with one coverage edge and no unresolved subitems. The canonical writer recorded
declaration pin
`sha256:56d1fe995397544a89849ab81bb95afd04df1b78fb4bb78fff0dc86b82fdb0f9`.
The command reused the cached Lean report and changed zero blueprints.
`git diff --check` returned 0. The full command log is retained in the attempt
directory as `cover-a2.log`; command success is not a fidelity judgment.

## A3: Ordered positive quadruple

Atom: `5f5912050d91b5f8998e6799d12c40e766fa4d65798ff890b506a56c3bc0ed3c`.
`make show-atom` returned 0 with the full raw/normalized body and no initial
coverage. The body explicitly assumes `a >= b >= c >= d >= 1`, boxes the
hypothesis `abcd = a+b+c+d` as (111), and then boxes the tuple conclusion.

Frozen declaration GID:
`D5/S3/Arith/GoldenResource/FourFactorSumProductBalance.sorted_positive_sum_product_classification`.
The actually read state file is
`Golden/Frozen/state/D5/S3/Arith/GoldenResource/FourFactorSumProductBalance.lean.json`,
with module pin
`sha256:1c446108a1b0a50141da4dc8d497c3e770561cfddf55c2d59193e24ee4fe2ea6`.
The whole module was read with `git show origin/dev:` at that module path,
including the nominated signature through `:= by` (lines 53-57).

| Source clause | Lean binders | Lean hypotheses / conclusion | Label |
| --- | --- | --- | --- |
| Ordered positive integers a >= b >= c >= d >= 1 | `a b c d : Nat` | `hd : 0 < d`, `hdc : d <= c`, `hcb : c <= b`, `hba : b <= a`; on Nat, `0 < d` iff `1 <= d` | equivalent |
| Box (111), hypothesis abcd = a+b+c+d | the same four naturals | `h : a+b+c+d = a*b*c*d`, by equality symmetry | equivalent |
| Box, conclusion (a,b,c,d) = (4,2,1,1) | every quadruple satisfying the preceding hypotheses | `a=4 AND b=2 AND c=1 AND d=1`, equivalent by tuple extensionality | equivalent |
| Title's uniqueness and existence, within the body's ordered domain | ordered positive Nat quadruples | Classification gives uniqueness; the displayed tuple satisfies the ordering and has sum 8 = product 8 | equivalent |

Quantifier and endpoint audit: this is a universal implication over four
naturals, not an existential or real-valued classification. The three order
inequalities are non-strict, so equal coordinates remain allowed. Positivity of
all four entries follows from `0 < d` and the order chain; d=1 is included.
There is no added hypothesis. Equality of sum and product is exact in both texts.
Existence of the displayed solution is direct numeral arithmetic; the frozen
module also contains an explicit inhabited-domain example. No claim that the
title means literal uniqueness without ordering is made (permutations would
contradict that reading).

Fidelity verdict: full match. Proposed use `proof_shape: bind-only`,
`escape_witness: null`,
`admission_basis: not-applicable(cover of an existing frozen declaration)`.
The direct frozen dependency is the GID above with its recorded module pin.
Writer receipt: `make cover-batch ATOMS=<attempt-1>/a3-cover.tsv
BASE=1bb54f920527c303ebaec4e5388d48fcbee0df04` returned 0 and `status=applied`.
The one-row TSV names only this atom and declaration. The atom migrated from
`residual-open` to `absorbed-closed`, with one edge and no unresolved subitems.
The writer's declaration pin is
`sha256:8ded602bc1d7c17f7e80f170c674f3785b55e2f3b00a5836c0e032d8ec7c5a8e`.
It reused the same cached Lean report and changed zero blueprints.
`git diff --check` returned 0; the only ledger delta at this checkpoint is A3.

## B1: U1 positive stitching, dossier only

Atom: `c352d304105e02cbbcb0607e31a1e217adb85d4b344ba0d75c23ba4420dbf0e1`.
`make show-atom` returned 0 with the complete raw/normalized body and empty
coverage. Its sole box, U13, says
`G_(N+1) >= 0 iff delta_N := d - b^* G_N^(-1) b >= 0`.
The directly read source context, `QUANTUM-RH.md:29550-29665`, fixes
`G_N > 0` and `G_(N+1) = [G_N,b; b^*,d]`. Here `*` on vectors/matrices means
conjugate transpose, and matrix nonnegativity means Hermitian positive
semidefiniteness. The scalar d is real as a self-pairing. No new d>=0 premise is
needed for the equivalence.

Frozen candidate GID:
`D5/S3/Weil/ZetaLinear/ExactStickyReduction.exact_sticky_reduction`.
The actually read state file is
`Golden/Frozen/state/D5/S3/Weil/ZetaLinear/ExactStickyReduction.lean.json`, pin
`sha256:311ed2863e85f005429c5613aacc27d7980b6ceba46355745055ba29b96d7984`.
The full frozen module was read with `git show origin/dev:`, including the
definitions and the candidate signature through `:= by`. It quantifies over
two real inner-product spaces HP,HQ and four real-linear maps APP,AQP,AQQ,AQQInv.
Its exact hypotheses are:

```text
hQQNonneg : forall q, 0 <= inner Real (AQQ q) q
hQQSymm   : forall x y, inner Real (AQQ x) y = inner Real x (AQQ y)
hQQInv    : AQQ.comp AQQInv = LinearMap.id
```

Its conclusion is a conjunction. The first member is universal nonnegativity
of `blockEnergy` iff universal nonnegativity of `schurEnergy`; the second is
equality of `negativeIndex`. Neither member literally names a complex matrix
or the scalar delta_N.

The required transport, in order:

1. Retain every source complex vector and every finite N. Set HP to Complex and
   HQ to `EuclideanSpace Complex (Fin N)`, both regarded as real vector spaces
   by scalar restriction. HP is one complex dimension, hence two real
   dimensions. This does not mean replacing complex coordinates by real ones.
   The Euclidean wrapper matters: the default norm on a bare function space is
   not the required Euclidean norm.
2. On HQ use `inner_R(u,v) = Re(sum_i conj(u_i)*v_i)`; on HP use
   `inner_R(z,w) = Re(conj(z)*w)`. These are restrictions of the complex
   Euclidean inner products. Squared norms are `sum_i |u_i|^2` and `|z|^2`.
3. Choose `APP(z)=d*z`, `AQP(z)=b*z`, `AQQ(x)=G_N*x`, and
   `AQQInv(x)=G_N^(-1)*x`. Matrix multiplication supplies complex-linear maps;
   restrict their scalars to obtain the real-linear maps required by the
   signature, without changing any underlying function.
4. Derive `hQQNonneg` from `G_N>0` (at zero the energy is zero), `hQQSymm` from
   Hermitian symmetry, and `hQQInv` from the finite-dimensional inverse
   identity `G_N*G_N^(-1)=I`. Strict positive definiteness ensures invertibility.
   These are consequences of the source setting, not extra assumptions.
5. Swap source coordinates `(x,z)` to theorem coordinates `(z,x)`. This is a
   bijection on the full carrier. Expansion of the frozen definition gives
   `blockEnergy(z,x) = d*|z|^2 + 2*Re(conj(z)*(b^* x)) + x^* G_N x`.
   This is the real value of `(x,z)^* G_(N+1) (x,z)`. Therefore universal
   nonnegativity of this energy is exactly the left side of U13.
6. Put `r=G_N^(-1)*(b*z)`. The frozen reduced energy is
   `d*|z|^2 - inner_R(G_N*r,r)`. Since `G_N*r=b*z`,
   `(G_N*r)^* r = (b*z)^* G_N^(-1) (b*z)
   = |z|^2 * (b^* G_N^(-1) b)`. The inverse of a Hermitian invertible matrix is
   Hermitian, so `beta=b^* G_N^(-1) b` is real. Taking real parts identifies
   `schurEnergy(z) = (d-beta)*|z|^2 = delta_N*|z|^2`.
7. Use only `(exact_sticky_reduction ...).1`. It gives both directions of the
   equivalence between nonnegativity for every `(z,x)` and for every z after
   the identifications above.
8. Translate `forall z:Complex, 0 <= delta_N*|z|^2` to `0 <= delta_N`.
   Necessity uses z=1. Sufficiency uses the nonnegativity of every norm square.
   Reverse all identifications to recover both directions of U13, including
   the zero-delta boundary.
9. Do not use the second, `negativeIndex`, conjunct. Its definition measures
   dimensions of real negative subspaces. It cannot simply be read as the
   number of negative complex eigenvalues; realification changes dimensions.

Clause classification: U13 is **equivalent after these transports**, not
verbatim. Both iff directions and both non-strict inequalities are retained.
All complex b,x,z, all real d, and the source finite positive-definite matrices
remain in the quantifier domain. No real-coordinate restriction, d>=0 premise,
or singular-matrix extension is inserted. The theorem's more general abstract
spaces do not themselves certify the finite complex-matrix interpretation.

Recommendation: **needs a Lean bridge**. The missing item is a typed, elaborated
identification of complex Hermitian matrix positivity with the real energies,
including the block swap, inverse premises and scalar reduction. The written
transport gives no mathematical counterexample; it also supplies no checked
bridge. Proposed reuse is `proof_shape: bind-only`, `escape_witness: null`,
with the candidate GID and module pin above as the direct frozen dependency;
`admission_basis: not-applicable(dossier only)`.

No coverage operation was executed for this atom. Its migration is
`residual-open -> residual-open`, with `coverage_gids: []`. No U14 realization,
singular/pseudoinverse variant, complex inertia count, or global arithmetic/RH
criterion is covered by this dossier.

## B2: Projected dynamics, dossier only

Atom: `7b2657006891568aa395dfd9fa14bde9d9d23d2ade0c449b00f7cdf5c616baec`.
`make show-atom` returned 0 with the complete raw/normalized body and empty
coverage. The source has arbitrary `T:X->X` and `pi:X->Y`, and asks whether a
map `Tbar:pi(X)->pi(X)` exists satisfying box (10), `pi o T = Tbar o pi`,
iff box (11), `pi(x)=pi(y) -> pi(Tx)=pi(Ty)`, holds for all x,y.

Frozen candidate GID:
`D5/S0/Rewriting/Quotients/DynamicsDescent.dynamics_descends_iff`.
The actually read state file is
`Golden/Frozen/state/D5/S0/Rewriting/Quotients/DynamicsDescent.lean.json`, pin
`sha256:9b68af3f9f0957494c5bd40f72876714752f0082c0d8ebdd1123463365fc025e`.
The whole frozen module was read with `git show origin/dev:`, including this
signature through its `:= by`:

```text
{X B : Type*} (quotientMap : X -> B) (update : X -> X)
(hSurjective : Function.Surjective quotientMap) :
(ExistsUnique fun descended : B -> B =>
  quotientMap o update = descended o quotientMap) <->
  forall x y, quotientMap x = quotientMap y ->
    quotientMap (update x) = quotientMap (update y)
```

The required transport, in order:

1. Retain arbitrary source carriers X,Y and both maps T,pi. Neither boxed
   formula imposes a metric, inner product, smoothness, linearity, invertibility,
   finite-state restriction or rewriting rule. The S0 module namespace does
   not add any such premise to its actual binders.
2. Set `B=Set.range pi`, the subtype `{y:Y | exists x:X, pi x=y}`, and
   `q:X->B` by `q(x)=(pi(x), witness x)`. This represents precisely the source
   codomain pi(X); X is not restricted.
3. For any b:B, its range-membership witness gives x with `pi(x)=b.val`.
   Subtype extensionality gives `q(x)=b`, so q is surjective. This does not
   require pi to be onto all Y and does not assume X is nonempty.
4. Identify `q(x)=q(y)` iff `pi(x)=pi(y)`: apply `Subtype.val` for one direction,
   subtype extensionality for the other. Apply the same identification to
   T(x),T(y). Thus box (11) is exactly the frozen right-hand side for q,T,
   with universal x,y and implication direction unchanged.
5. Instantiate `dynamics_descends_iff` with `quotientMap=q`, `update=T`, and
   the surjectivity proof above. No inner product is introduced. Unlike B1,
   this statement is an iff, not a conjunction with an unused second member.
6. Make box (10) well typed. For `f:B->B`, the equality in B is
   `q o T = f o q`. Its Y-valued form is
   `pi o T = Subtype.val o f o q`. Function extensionality and subtype
   extensionality identify these equalities. The source's informal use of pi
   at both codomains has to be made explicit; replacing B by all Y would be
   a different claim.
7. From frozen `ExistsUnique` obtain the source `Exists` by retaining the
   map and commuting equality. Conversely, suppose f commutes. If g also
   commutes, every b:B has b=q(x), hence
   `g(b)=g(q(x))=q(Tx)=f(q(x))=f(b)`. Surjectivity and function extensionality
   prove g=f, so the source existence assertion implies existence and
   uniqueness on exactly this codomain.
8. Both directions of the frozen iff now yield both directions of the source
   iff. Empty X and empty range remain allowed; no point outside an existing
   range witness is needed. The frozen proof chooses representatives using
   `Classical.choose`; it establishes existence and is not an executable
   geometric algorithm.

| Box | Frozen component after transport | Label |
| --- | --- | --- |
| (10), existence of a commuting Tbar on pi(X) | Left side, `ExistsUnique`, after range restriction, coercion identification and automatic uniqueness | equivalent |
| (11), preservation of every pi-fiber under T | Right side, all x,y with equality of q-values, after subtype extensionality | equivalent |

Recommendation: **needs a Lean bridge**. The written transport exposes no
mathematical mismatch in (10)-(11), but the range/coercion and
Exists-to-ExistsUnique identifications have not been elaborated. Both directions
of the frozen iff are used; uniqueness is discarded for the source existence
reading and shown automatic for the converse identification. There is no
separate unused conjunct. No geometric regularity, distance preservation or
computability follows from these equations alone.

Proposed reuse is `proof_shape: bind-only`, `escape_witness: null`, with the
candidate GID and module pin above as the direct frozen dependency;
`admission_basis: not-applicable(dossier only)`. No coverage operation was
executed for this atom. Its migration is `residual-open -> residual-open`, with
`coverage_gids: []`. The unelaborated bridge and any stronger interpretation of
the title's "independently execute" wording remain uncovered.

## Final local verification

At content checkpoint `412fcb588a47cccc596fdd3467aa9dc4eb09d348`, a structured
Ruby YAML/JSON inspection (`<attempt-1>/verify-ledger.rb`, exit 0) compared the
five ledger records with baseline `1bb54f920527c303ebaec4e5388d48fcbee0df04`.
It found exactly three `residual-open -> absorbed-closed` migrations and four
coverage edges with the declaration pins recorded above. All three records
retain their original noncoverage fields and have no unresolved subitems.
Both B records remain at their original residual paths with empty coverage and
are byte-identical to baseline.

The complete baseline diff, with rename detection disabled, is exactly the six
A-ledger old/new paths and this report. There are zero `.lean`, frozen-state,
atom-CAS, B-ledger, or other tracked changes. `git diff --check` returned 0 and
the tracked working tree was clean. This inspection verifies structure and
scope; it does not verify mathematical fidelity.

Additional literal-declaration search, at the initially resolved origin/dev:

```text
git grep -n -P '\btheorem\s+(golden_resource_5040_unique_maximum_of_price_interval|sorted_positive_sum_product_classification|exact_sticky_reduction|dynamics_descends_iff)\b' origin/dev -- D5
```

Result: four lines, exactly one per named declaration, exit 0. The same-feature
positive and negative controls are recorded in A1. These are declaration-text
readings, not claims about all semantic references or an exhaustive search.

Late `git fetch origin dev` returned 0 and resolved origin/dev to
`bec7677043c96526c256a3d6c413c965aead4c67`. The five nominated module/frozen
paths and all five atom paths have no diff between the original baseline and
that fetched dev. `git merge-tree --write-tree origin/dev HEAD` returned 0,
tree `3614d67d99b21046581955744651300bf8981a60`, at the content checkpoint above:
no merge conflict was reported. No merge, rebase, deposit or freeze was executed.

Checkpoint pushes, each with exit 0:

| Atom | Audit / dossier commit | Coverage receipt commit |
| --- | --- | --- |
| A1 | `dedb9237970cfd674f1fca9bfd8b1f734f2b08dd` | `e62051ae71a5c080e8c0d4c9050f919e70a44cda` |
| A2 | `c9b16aa9c60b8ecedc401921ff9332895de25f3b` | `1a705e286cd4d4f8b9af3b7db2d37aac7c139748` |
| A3 | `44b6214a083b6b12af116c5425e7614a26a6f8e6` | `5399bac8f45a6fdb030bba96d807de4c7aedcf72` |
| B1 | `87ec5696950bd10a5ad4fe8cc7adf380150eadeb` | none; cover prohibited |
| B2 | `412fcb588a47cccc596fdd3467aa9dc4eb09d348` | none; cover prohibited |

The preregistration was separately pushed as
`ee9e8ed394b3655f677823b6e73cb5ab1add423e`. All five show-atom commands and all
three canonical cover commands returned 0. PR opening uses `make pr-open`
without `AUTO_MERGE`; its command exit, required-check result, final remote head
and PR number are delivery-time receipts in the attempt's `result.json` and
`pr-open.log`. This report makes no claim of merge.

## Nonclaims

- No claim that `make cover` judges fidelity.
- B-group atoms are not covered by this worker.
- No new theorem, proof, deposit, freeze, or implication to RH is claimed.
- No exhaustive repository or literature search is claimed.
- No independent review or multi-model consensus is claimed.
- No automatic merge or merged-PR outcome is claimed.
