---
slug: oeis-a381361-hanna-all-odd
bibkey: hanna2025a381361
doi: null
url: https://oeis.org/A381361/internal
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/HannaA381361AllOdd.result
---

## Problem

Paul D. Hanna's OEIS A381361, revision 25, first COMMENTS observation says:

> All terms appear to be odd.

Its NAME defines the exponential generating function by
$A(x)=\exp(\int_0^x\operatorname{abs}((A(t)^2)^{-1})\,dt)$,
where absolute value acts coefficientwise. The coefficients are
$a_n=n![x^n]A$ and the offset is zero. The source has no identified DOI or arXiv identifier.
Preregistration: [#24232](https://github.com/the-omega-institute/trureturing/issues/24232).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Formal exponential of the primitive of the unsigned reciprocal square | `IsSourceSeries` | Literal rational formal equation, including coefficientwise absolute value. |
| Primitive normalized at zero | Existential primitive with zero constant coefficient | Fixes the formal integration constant. |
| $A(0)=1$ | First conjunct of `IsSourceSeries` | Normalization supplied by the exponential equation. |
| All terms are odd | `claim`, proved by `result` | Every source solution and every natural index has $a_n=2z+1$ for an integer $z$. |
| EGF coefficients and offset zero | `IntegralEGFComposition.eCoeff`, natural index binder | Factorial normalization; index zero is included. |
| Source existence | First conjunct of `claim` | Prevents vacuity and is proved without assuming integrality. |

## Motivation

The settling declaration is `D5.S1.Recurrence.Parity.HannaA381361AllOdd.result`.
The module has generality `I`, utility `none`, and admission basis
`open-problem-resolution (#24232; Proved)`. Its proof shape is `bind-only`:
the external named settlement is admitted under the open-problem-resolution exception.
The supporting owners supply normalized contraction, formal EGF arithmetic,
unit inversion, linear ODE uniqueness and characteristic-two square collapse.
The source note is `Library/Certificates/hanna2025a381361.md`.

## Gap

The literal implicit rational equation requires an existing solution and integral
EGF coefficients before reduction modulo two is meaningful. Square collapse alone
does not identify the source coefficients with an integer recurrence. The theorem
includes source existence and the all-solution parity statement.

## Route

For integer sequences write the Hurwitz product as
$(u*v)_n=\sum_{k=0}^n\binom nk u_kv_{n-k}$.
Construct the normalized sequence by
$c=a*a$, $b=c^{-1}$ in the Hurwitz algebra, and
$a_{n+1}=(a*|b|)_n$, with $a_0=1$.
The update at index $n$ uses only indices through $n$; normalized contraction gives
existence and uniqueness. The EGF multiplication and inversion identities, and
positivity of factorials under absolute value, identify this recurrence with
$A'=A\operatorname{abs}((A^2)^{-1})$ over the rationals.
A zero-constant primitive and linear ODE uniqueness recover the literal source equation.
This proves integrality rather than assuming it.

Modulo two a normalized Hurwitz square is the unit sequence. Its inverse is the
unit sequence too, and integer absolute value preserves reduction modulo two.
Consequently the update reduces to $a_{n+1}=a_n$ modulo two. The initial value is one.

## Falsifier

A rational source solution with a nonintegral or even EGF coefficient at any natural
index contradicts the proved `claim`. A failed identity for a different ordinary
convolution or a differently normalized primitive concerns a different statement.

## Evidence

The kernel-checked public theorem is
`D5.S1.Recurrence.Parity.HannaA381361AllOdd.result`.
The private lemmas named below are compiled in that module and are consumed by its
settling proof. The four-slot escape audit is unfinished for this theorem and the
published owner declarations; [#26285](https://github.com/the-omega-institute/trureturing/issues/26285)
identifies the missing exact bridges, lawful enrolled readouts and sensitivity evidence.
No registration is claimed `declared_validated`.

### Finite experiment

[Exact-check directory at commit ad87319c65b998ecf5ac94e33c68764f9e7d2ccc](https://github.com/the-omega-institute/trureturing-experiments/tree/ad87319c65b998ecf5ac94e33c68764f9e7d2ccc/docs/reports/hanna-a381361-odd).
The immutable `check.py` and `source_terms.tsv` blobs were executed from the
experiments clone's `.scratch/op-hanna381361b-ad87319/` directory.
Command: `python3 /Users/auric/trureturing-experiments/.scratch/op-hanna381361b-ad87319/check.py`;
exit code 0; script SHA-256
`f87c0e74aea97126b19b5b3b8aa490cfec99e71c1eb567b0811cc7bf2adfef72`.
The source table SHA-256 is
`93779794cd57e856400e4156f8eb50cc80971ebed6549b7c2f6647ce6f71dfd4`.
All 501 source terms agree at indices $0,\ldots,500$ and are odd;
the positive-degree square and inverse coefficients are even through degree 500.
The inverse identity is checked through degree 500, the derivative recurrence
through index 499, and the displayed reciprocal-square coefficients through index 10.
The independent ordinary rational map stabilizes and agrees with the Hurwitz
construction through degree 18. These are finite computations, not the universal proof.

## Triage

| Item | Status | Evidence kind and scope |
| --- | --- | --- |
| Positive-degree Hurwitz squares vanish modulo two; inverse and absolute value preserve reduction, giving successor parity | proved | Kernel-checked private `square_mod_two`, `seqInv_one`, `egfMul_one_right`, `next_mod_two`, and `sequence_odd`, on the live path to public `result`. |
| The literal rational source solution exists uniquely and has integral EGF coefficients | proved | Kernel-checked private `integral_source_exists_unique`; public `result` uses its existence and integrality. No integrality hypothesis occurs in `claim`. |
| `next_mod_two` holds for every integer sequence with $a_0=1$, before imposing the recurrence | proved | Kernel-checked private `next_mod_two`; its only sequence hypothesis is $a_0=1$. |
| Finite source agreement and oddness through index 500; independent rational-map agreement through degree 18 | computed | The finite experiment above, exit 0 and pinned script SHA-256; this is not a universal claim. |
| Every positive even reciprocal exponent has an analogous all-odd property | open | No such family theorem is delivered. |
| Sibling #23762, divisibility by five for $n>4$, and source elliptic, algebraic and asymptotic equivalences | open | Separate obligations; no declaration here settles any of them. |

### What the settlement shows

**Proved in Lean:** the decisive parity update holds for every normalized integer
input sequence, and the source equation has a unique rational solution with integral
EGF coefficients. The source-specific oddness theorem therefore needs no assumed
integrality, convergence or elliptic representation. Uniqueness and the stronger
update statement are supporting private lemmas, not additional public settlements.

**Explanation:** Hurwitz square collapse supplies the arithmetic mechanism and
absolute-value invariance transports it through the nonlinear source equation.
The all-odd conclusion includes index zero. This argument does not establish the
modulo-five tail assertion, any analytic asymptotic or a uniform reciprocal-exponent family.
The preregistration's source screen identifies no theorem whose proof here depends
on treating those separate assertions as established.

**Literature reading:** #24232 records the OEIS source, related entries,
arXiv metadata and full-text screens, Semantic Scholar, MathOverflow, Zenodo,
repository and bounded global-code searches. No earlier parity settlement was
identified within that recorded scope. Service failures and unread or unindexed
material supply no negative evidence.

## ASSUMED-UNVERIFIED

Literature completeness and historical priority beyond the sources actually read
in #24232 are `ASSUMED-UNVERIFIED`. OpenAlex and MathDB failures, bounded corpus
coverage and metadata-only screens prevent an exhaustive prior-art claim.
The four-slot escape audit remains unfinished under #26285 and is separate from
kernel verification and the mathematical settlement.
