# Degree-five finite free commutator

This implementation proves only degree five of Conjecture 5.3 in Campbell,
Morales and Perales, *Even Hypergeometric Polynomials and Finite Free
Commutators*, arXiv:2502.00254v2, DOI `10.3842/SIGMA.2025.108`.
The authorship, operation, literature search scope and preregistered witness
are recorded in `r18-quintic-preregistration.md` in this directory.
Canonical verified locator scope: v2 printed page 19, Notation 5.1; page 20,
Conjecture 5.3 and Theorem 5.6; page 21, Remark 5.7. Section 2.1 defines
`P_n` as monic polynomials of degree n, with `P_n(R)` requiring all roots real.

## Result and proof

The public theorem is
`D5/S3/Zeros/Convolution/FiniteFreeCommutatorDegreeFive.real_rooted`:
for arbitrary `p q : R[X]`, `RealRooted5 p` and `RealRooted5 q` imply
`RealRooted5 (square5 p q)`. `RealRooted5` is an actual product of five real
linear factors. The result includes repeated roots and arbitrary translations.
It does not assume the factorization condition of Theorem 5.6.

The first bind-only probe checked the pullback of the frozen quartic bound.
It gives `u<=0` and `-3u^2/20<=w<=9u^2/20`, but the scalar assignment
`u=-1,w=9/20` satisfies these and violates the needed sharp upper bound.
The probe built successfully before implementation; it was not submitted as
a content module. This failure only rules out that scalar implication.

The preregistered escape witness is proved without weakening its constant:
`w <= (4/15)*u^2` for every centered real-rooted quintic
`X^5+uX^3+vX^2+wX+t`. Sort its five roots as `a<=b<=c<=d<=e` and let
`A=b-a,B=c-b,C=d-c,D=e-d`. The zero-sum condition gives the exact identity

```text
30*(a^4+b^4+c^4+d^4+e^4)-7*(a^2+b^2+c^2+d^2+e^2)^2 = 8*F,
F = A^4+3A^3B+2A^3C+A^3D+3A^2B^2+4A^2BC+2A^2BD
  + A^2C^2+A^2CD+ABC^2+ABCD+ABD^2+2ACD^2+AD^3
  + B^2C^2+B^2CD+B^2D^2+4BCD^2+2BD^3+3C^2D^2+3CD^3+D^4.
```

All 22 monomials are nonnegative. Coefficient comparison and Newton identities
give `sum r_i^2=-2u` and `sum r_i^4=2u^2-4w`. These imply the sharp estimate.
The included Lean examples verify roots `(2,2,2,-3,-3)`, coefficients
`u=-15,w=60`, and exact equality `60=(4/15)*(-15)^2`.

Multiplicity-aware Rolle in pinned Mathlib makes `p'/5` the real-rooted
quartic `centeredQuartic (3u/5) (2v/5) (w/5)`. The live frozen consumer is
`FiniteFreeCommutatorDegreeFour.centered_quartic_invariant_bounds`.
Its first two conclusions give `u<=0` and `0<=3u^2+20w`. The new estimate
gives `3u^2+20w<=25u^2/3`.

The source definitions, including both multiplicative convolutions, yield

```text
Sym5(p) = X^5+2uX^3+(2w+3u^2/10)X,
z5 = X^5-(125/6)X^3+(50/9)X,
square5(p,q) = X^5-(5uU/6)X^3+((3u^2+20w)(3U^2+20W)/450)X.
```

Put `I=3u^2+20w`, `J=3U^2+20W`, and
`Delta=(5uU/6)^2-4*I*J/450`. The exact remainder identity

```text
Delta-25u^2U^2/324 = (2/225)*((25u^2/3)*(25U^2/3-J)+J*(25u^2/3-I))
```

proves the requested discriminant lower bound. Nonnegative `s,t` factor the
output as `X*(X^2-s)*(X^2-t)`, exhibiting roots `0,+/-sqrt(s),+/-sqrt(t)`.
The proof uses non-strict inequalities throughout and divides only by fixed
nonzero numeric constants. In particular it includes zero discriminant.

Finally, translation by `-a/5` centers an arbitrary quintic whose quartic
coefficient is `a`. Translation preserves its five real factors, and a
definition-derived calculation proves that `Sym5` is translation-invariant.
This completes the general, uncentered degree-five statement.

## Admission and provenance

`proof_shape: content`; `admission_basis: escape-witness`.
The observed escape witness is exactly the preregistered sharp coefficient
estimate. Its proof supplies a new nonnegative gap certificate, and its upper
bound is used in the discriminant remainder on the final theorem's live path.
`centered_expansion` is a bind-only normalization companion, consumed by
`centered_factorization`; it is not an independent admission claim.
The remaining public theorems inherit the sharp estimate on their proof paths.

`computational_content.kind: certified-instance`.
`question_answered`: Conjecture 5.3 at n=5, registered before implementation.
`terminal_result`: the module's `real_rooted` theorem.
`dominating_theorem_search`: not-found-in-searched-scope; repository,
pinned Mathlib, GitHub Lean sources, arXiv and OpenAlex, with positive controls.
The bounded literature search found no proof of this case; it does not establish
worldwide priority. The supplied random experiments were not used as premises.

The implementation was produced by one Codex worker without a named skill or
independent local review agents. The dispatch supplied the target estimate
and proposed consumer. The worker checked the paper and constructed the proof.

`make lean` verified all seven public theorems. Actual `#print axioms` output
for each is `[propext, Classical.choice, Quot.sound]`. The successful full
module build reported 79 seconds on the supplied warm cache, with concurrent
host workloads; this excludes the wrapper and replay overhead.
`make lean-report` also passed and recorded all seven public theorem identities
with those same axioms. The repository selftest passed independently.
An additional worker-local Lean audit read elaborated proof constants,
inlined local private helpers and definitions, stopped at other public local
theorems for direct dependencies, and separately traversed them for reachable
dependencies. It confirms the live named frozen consumer. Exact per-theorem
GIDs and declaration statement IDs are in the worker result envelope.


## Direct frozen dependencies

The following IDs come from the pinned report for frozen module
`D5/S3/Zeros/Convolution/FiniteFreeCommutatorDegreeFour`, whose module identity is
`sha256:e4f15f5c0461a866887270b3ea9714ad3cb9c7bf4a40afe95cc84c3488442c13`.
Each selector below extends that module GID. Generated equation lemmas and
frozen definitions are included, so this table does not conflate imports with
proof dependencies.

| Code | GID Selector | Declaration statement_id |
| --- | --- | --- |
| F1 | `multiplicativeConvolution` | `sha256:ba56b956857ca58b3249d369f8dbad629876e52c8b1c88ec2a2494f78401b522` |
| F2 | `symmetrize` | `sha256:e9db27e70bca5288a1bc78fb5b5f63f1dbfc300b6b176a87a46b3231ebae4bab` |
| F3 | `commutatorKernel` | `sha256:e57b68ae1abe9eba25522e70a4860383bc3dbff45b0d0fb9598b0a3ba408024b` |
| F4 | `elementaryCoeff` | `sha256:6edacf40fa3575becc3b3548435bf99326ea1e208a06ab9255b2ff81051fe2c9` |
| F5 | `additiveConvolution` | `sha256:25a49b95cd06b2a42797145a0f0d8ea2f69fd2aad30577f099a73d629d88b267` |
| F6 | `dilate` | `sha256:cfeef8d70acd59c3974ef7fce414e3607d72c81cb6d6f9e6d41be3b66c990cee` |
| F7 | `symmetrize.eq_1` | `sha256:5538c35520887da1fc5c9274ec11cffbb8b0ea7c13fe6aad201abbc91e8a28fb` |
| F8 | `centered_quartic_invariant_bounds` | `sha256:54602f574b2a6eded62969fdd8546beb4ef610d1968023fb9decdcad686b3b0c` |
| F9 | `RealRooted4` | `sha256:93ca733d793d6c29fd3b1df417af46618f95dd7f0b176eae14f3ad2abaf51e8b` |
| F10 | `centeredQuartic` | `sha256:0c58e1f978d92afe95e2dbdbc3678aa758fd162ac521b2cf4357ebe128246d25` |
| F11 | `centeredQuartic.eq_1` | `sha256:006ca684c7725536250645ede5509104e98a339283d34dc5f29c0eff62f5748e` |

Each theorem below extends `D5/S3/Zeros/Convolution/FiniteFreeCommutatorDegreeFive`.
Direct traversal expands private helpers and definitions but stops at other
public theorems of this module; their directed edges are listed separately.

| Public Theorem | proof_shape | Direct Frozen Codes | Direct Public Prerequisites |
| --- | --- | --- | --- |
| `centered_quintic_coefficient_bound` | content | none | none |
| `centered_expansion` | bind-only | F1, F2, F3, F4, F5, F6, F7 | none |
| `centered_quintic_invariant_bounds` | content | F8, F9, F10, F11 | `centered_quintic_coefficient_bound` |
| `centered_discriminant_bound` | content | none | `centered_quintic_invariant_bounds` |
| `centered_factorization` | content | F1, F2, F3 | `centered_quintic_invariant_bounds`, `centered_discriminant_bound`, `centered_expansion` |
| `centered_real_rooted` | content | F1, F2, F3 | `centered_factorization` |
| `real_rooted` | content | F1, F2, F3, F5, F6, F7, F4 | `centered_real_rooted` |

Following these edges reaches both the sharp estimate and frozen F8
(`centered_quartic_invariant_bounds`) from the final theorem. Frozen definitions
in a conclusion's type are recorded as dependencies without claiming them as
new mathematical content.

This handoff is implementation plus Scribe, not a freeze or coverage operation.
The task explicitly forbids edits under `Golden/Frozen/**`; none were made.
No Library note or atom coverage was created. Final check outputs, failed
attempts, command exit codes, PR status and remaining limitations belong to the
worker-owned attempt artifacts.
