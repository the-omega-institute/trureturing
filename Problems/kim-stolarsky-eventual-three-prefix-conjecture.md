---
slug: kim-stolarsky-eventual-three-prefix-conjecture
bibkey: kimstolarsky2026nicomachus
doi: 10.5281/zenodo.21678529
url: https://math.colgate.edu/~integers/aa98/aa98.pdf
triage: theorem
motivation_gids:
  - D5/S1/Depth/ContinuedFractions/QuadraticImpliesPeriodic.completeQuotient
---

# Kim–Stolarsky's eventual three-prefix conjecture

## Problem

Seon-Hong Kim and Kenneth B. Stolarsky, *A Balanced Three or More-term
Generalization of Nicomachus' Identity*, Integers 26 (2026), A98,
Theorem 1 and Remark 3, pose the same conjecture as Theorem 1 and Remark 4
(`cfrac5`) of arXiv:2511.15133v1, *A Balanced Three-term Generalization of
Nicomachus' Identity*. These are one problem, preregistered before the
mathematical probe in [issue #28129](https://github.com/the-omega-institute/trureturing/issues/28129).

Put $T_j=j(j+1)/2$. For integers $s\geq2$, the original real polynomials are

$$
L_{s,o}(x)=\sum_{j=1}^{s}(2j-1)^3+x^3+
  \sum_{j=2}^{s}(2j-2+(j-1)x)^3,
\qquad
R_{s,o}(x)=(T_{2s-1}+(1+T_{s-1})x)^2.
$$

$$
P_{m,o}(x)=\sum_{j=0}^{m}(4j+1+jx)((j+1)(j-2)+j^2x),
\qquad Q_m(x)=xP_{m,o}(x)-x^2+x^3.
$$

The “for large n” target is: there exist real sequences $l_n,r_n,q_n$
and an integer $N\geq1$, all three sequences tending to $-4$ as
$n\to\infty$, such that for every integer $n\geq N$, with
$m=10^{2(2n+1)}=10^{4n+2}$, simultaneously

$$
L_{m+1,o}(l_n)=0,\qquad R_{m+1,o}(r_n)=0,\qquad Q_m(q_n)=0,
$$

and the ordinary simple continued fractions of their negatives have prefixes

$$
-l_n=\left[4;75\cdot10^{4n},3,4,1,
  \frac{(15\cdot10^{2n})^2-23}{101},\ldots\right],
$$

$$
-r_n=\left[4;50\cdot10^{4n}+2,
  \left\lfloor\frac{10^{4n+2}}7\right\rfloor-1,\ldots\right],
$$

$$
-q_n=\left[4;75\cdot10^{4n},3,
  \left\lceil\frac{6\cdot10^{4n+2}+100}{35}\right\rceil,\ldots\right].
$$

Each digit is the floor of the successive complete quotient, obtained by
inverting the preceding fractional part. Remainders before the last
specified digit must be nonzero; the remaining tail is unrestricted.
The literal source digits, original polynomial sums, $m+1$ shifts, root
limits and common eventual threshold are all retained. This dossier
targets that entire conjunction, not three separate settlements.

## Motivation

The frozen declaration
`D5/S1/Depth/ContinuedFractions/QuadraticImpliesPeriodic.completeQuotient`
supplies the floor-and-inverse recurrence used directly by `HasPrefix`.
It anchors the ordinary continued-fraction semantics independently of
the conjectured polynomials; no periodicity hypothesis is imported.
The eventual quantifier requires unbounded failures for a refutation,
rather than one finite numerical mismatch.

## Gap

The source explicitly conjectures these three prefixes. The bounded
literature and repository screen in the matching Library note found no
settlement in the accessed surfaces; the journal retains the conjecture.
This supports the preregistered external-problem admission proposal, not
an assertion of exhaustive worldwide modern-open status or priority.

## Route

For $m>10$, the actual shifted R square has positive linear coefficient
$1+T_m$, so its only distinct real root is

$$
r=-\frac{2(2m+1)(m+1)}{m^2+m+2}.
$$

For $y=-r$, exact algebra gives

$$
y-4=\frac{2m-6}{m^2+m+2},\qquad
\frac1{y-4}=\frac m2+2+\frac7{m-3}.
$$

Here $0<y-4<2/m$, and $m$ is even. The first two digits are
$4,m/2+2$, and the next complete quotient is $(m-3)/7$.
If $n=3k+2$, then $m\equiv4\pmod7$. Write $m=7a+4$; the actual
third digit is $\lfloor a+1/7\rfloor=a$, whereas the printed digit is
$\lfloor m/7\rfloor-1=a-1$. The private `r_failure` proves the mismatch
for every R root on this progression. The public `result : Not claim`
uses $n=3N+2\geq N$ to contradict every proposed common threshold.

## Falsifier

For every $N\geq1$, the admissible index $n=3N+2$ forces the third
R digit to differ from the displayed conjectured value by one. Root
selection cannot remove the discrepancy because the shifted R square
has only one distinct real root. Thus no branches and common threshold
can meet the complete conjunction. A finite example alone would not
supply this falsifier.

## Evidence

The source identity, exact original TeX and journal PDF hashes, locators
and bounded search readings are in `Library/Certificates/kimstolarsky2026nicomachus.md`.
The existing scoped compiled evidence identifies the closed theorem
`D5/S1/Depth/ContinuedFractions/KimStolarskyEventualPrefixRefutation.result`
with literal type `Not claim`, where `claim : Prop` is the complete target
above. Its axiom closure is `Classical.choice`, `Quot.sound`, `propext`.
This source binding does not assert freezing, canonical projection,
rendered fidelity, required CI success or integration.

## Triage

`theorem`; first-tier external named conjecture. The unique settling
declaration is `result`, with `proof_shape: bind-only` and proposed
`admission_basis: open-problem-resolution` under issue #28129.
The private bind-only helpers have real consumers: `residue` is consumed
by `result`, `parameter_large` by `r_failure`, and `r_failure` by `result`.
No helper supplies an escape witness or a separate settlement.

- **Proved — complete conjunction refuted:** the compiled `result` defeats
  every eventual threshold through the R root/prefix pair. It does not
  exploit absence of an L or Q branch or a false replacement polynomial.
- **Derived — mechanism:** the floor shift is residue-sensitive. At
  $n=3k+2$, the root's exact expansion is $[4;m/2+2,a,7]$ with $m=7a+4$;
  the alternative final-one representation retains the disputed digit $a$.
  The obstruction is before termination, not a rational-tail convention.
  The displayed bound $0<y-4<2/m$ also shows that this actual R branch
  tends to $-4$; that limit calculation is not a separate compiled theorem.
- **Open — nearest surviving statements:** the individual L and Q root,
  limit and prefix assertions are unresolved here, as is the even case.
  A corrected R digit $\lfloor(m-3)/7\rfloor$ and a restriction excluding
  the obstructed indices are possible follow-up targets; no corrected
  three-prefix conjecture is proved or registered by this result.
- **Open — consequences for neighbouring observations:** the three
  displayed prefixes cannot jointly justify an eventual assertion on the
  full source subsequence. The source's comparisons of later large digits
  and asymptotic ratios, and its even-termination observation, have no
  independent verification here. This refutation neither certifies nor
  refutes those separate observations or the source's polynomial identity.

## ASSUMED-UNVERIFIED

Worldwide modern-open status, exhaustive nonduplication and priority remain
ASSUMED-UNVERIFIED. The source screen is bounded as recorded in the Library
note. Individual L/Q assertions, the even case and corrected conjectures
remain unresolved. The resolution claim binds exactly the complete
eventual conjunction to the unique result; it is source metadata, not a
claim of publication readiness, a solved-count increment or KPI credit.
