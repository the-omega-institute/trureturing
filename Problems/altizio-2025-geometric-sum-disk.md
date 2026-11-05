---
slug: altizio-2025-geometric-sum-disk
bibkey: altizio2025stern
doi: 10.48550/arXiv.2511.03847
url: https://arxiv.org/abs/2511.03847v1
triage: theorem
motivation_gids:
  - D5/S3/Zeros/AltizioGeometricSumDisk.result
---

# Altizio's geometric-sum disk classification

## Problem

David Altizio, *Zeros of Stern polynomials in the complex plane*,
arXiv:2511.03847v1, Section 4.3, p. 20, Remark 4, states:

> One might suspect that |(z)_n| ≥ n|z| more generally whenever z ∈ B.
> However, numerical evidence suggests that the value min_{z∈B} |(z)_n/z|
> approaches 2π as n → ∞. It seems that this inequality is true only for
> n = 5, 6, and 7, but we do not have a proof.

Section 2 defines $(z)_n=1+z+\cdots+z^{n-1}$ for positive integers $n$;
Section 3 defines $B=\{z\in\mathbb C:|z-2|\le1\}$.
The settled statement is

$$
\forall n\in\mathbb N,\quad n>0\Longrightarrow
\left[\left(\forall z\in B,\ n|z|\le\left|\sum_{k=0}^{n-1}z^k\right|\right)
\Longleftrightarrow n\in\{5,6,7\}\right].
$$

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Positive integer $n$ | Natural $n$ with $0<n$ in `claim` | Exact positive range |
| $(z)_n=1+z+\cdots+z^{n-1}$ | The literal sum over `Finset.range n` | Includes its value $n$ at $z=1$ |
| $B=\{|z-2|\le1\}$ | `Metric.closedBall (2 : ℂ) 1` | The boundary is included |
| $|(z)_n|\ge n|z|$ for every $z\in B$ | Natural-to-real cast, complex norms, universal disk quantifier | Same inequality direction |
| Only $n=5,6,7$ | Biconditional with the three degree equalities | Sufficiency and necessity |
| Suggested $2\pi$ limit | Outside `claim` | Open |

`claim` is the only public definition and reproduces the source expression
literally. The private proofs use `geom_sum_mul` for that finite sum,
`Polynomial.dickson` for the boundary recurrence, the frozen `coeffL1` for
coefficient mass, and the frozen `quantitativeSeedRadius` for the positive
remainder parameter.

## Motivation

[Preregistration #20656](https://github.com/the-omega-institute/trureturing/issues/20656)
selects the degree classification in Remark 4. The settling declaration is
`D5.S3.Zeros.AltizioGeometricSumDisk.result : claim`.
Its admission basis is `open-problem-resolution (#20656; Proved)`.
The source's Proposition 8 already proves the two bounds for degrees five
and six; the classification includes degree seven and excludes every other
positive degree.

## Gap

This is a tier-1 named question in a published arXiv source. The source and
literature readings recorded in #20656 cover the arXiv version, the author's
dissertation, author/title and geometric-sum searches, citation indexes,
the related MathOverflow question and formal-conjectures. No settlement was
found in that searched scope. Literature completeness is
`ASSUMED-UNVERIFIED`.

## Route

Put $u=|z|^2$ on $|z-2|=1$. Then
$z+\overline z=(u+3)/2$ and $|z-1|^2=(u-1)/2$.
The sequence $P_n(u)=z^n+\overline z^n$ obeys the second-order Dickson
recurrence. The defect polynomial

$$
D_n(u)=u^n+1-P_n(u)-\frac{n^2u(u-1)}2
=|z-1|^2\bigl(|(z)_n|^2-n^2|z|^2\bigr)
$$

is nonnegative for degrees five, six and seven by the certificates below.
The disk meets the unit circle only at $1$, so the finite geometric sum has
no zero in the disk. The maximum modulus principle for $z/(z)_n$ extends
the boundary estimates to the closed disk.

For every excluded positive degree, the constant and linear terms of
$D_n(1+t)$ vanish and its quadratic coefficient is
$c_n=-n^2(n-5)(n-7)/48\le-1/2$.
Write $D_n(1+t)=t^2(c_n+tT_n(t))$ and let $M_n$ be the sum of absolute
coefficients of $T_n$. On $0\le t\le1$, $|T_n(t)|\le M_n$.
The reused radius $t=1/[4(M_n+1)]$ makes the defect negative.
The complex point
$z(t)=(4+t+i\sqrt{t(8-t)})/4$ has $|z(t)-2|=1$ and $|z(t)|^2=1+t$,
so it violates the bound.

The public surface is `claim` and `result`. All private helpers have live
consumers. Utility is `none`: the degree classification is uniform, and the
finite-degree polynomial identities have a real variable rather than a
closed numerical certificate.

## Falsifier

A mismatch in the finite-sum convention, positive-degree range, closed-disk
boundary, cast or biconditional invalidates source fidelity. A counterexample
in degree five, six or seven, or a proof of the universal inequality in any
other positive degree, refutes the classification. A prior settlement would
invalidate the claimed literature gap. Numerical samples do not settle the
unbounded quantifiers.

## Evidence

`D5/S3/Zeros/AltizioGeometricSumDisk.lean` and its Blueprint Scribe carry the
settling theorem with one `OpenProblemResolutionClaim(Proved)`.
The Library note is `Library/Zeros/altizio2025stern.md`.
The axiom closure of every public declaration is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

Escape audit unfinished:
[#20656](https://github.com/the-omega-institute/trureturing/issues/20656).
The sole target is `D5.S3.Zeros.AltizioGeometricSumDisk.result`.
The searched Iff, pointwise-order and dependent-family enrollments do not
supply a compiled faithful registration. A singleton-state dependent-family
candidate has a source-equivalence bridge but fails observational dependence.
A nonconstant reconstruction, exact source bridge, whole-family variation,
sensitivity and actual observational dependence remain missing. No Reg mirror
or `declared_validated` status is claimed.

### Supporting experiment

[Experiment directory at commit 65ee1fc450d3e106194a87a31f910d2ef1ba35bd](https://github.com/the-omega-institute/trureturing-experiments/tree/65ee1fc450d3e106194a87a31f910d2ef1ba35bd/docs/reports/altizio-2025-geometric-sum-disk).
The script is `check.py`, SHA-256
`cc441905676ba7ed3924ce669b140bf6869da609f92bfcfe8b162a57cd26181d`.
Its immutable Git object exists and has that digest. The command
`python3 /Users/auric/.sshx/1ec02b927de430d31aeec9d4/attempt-1/experiment_check.py`
executes those exact bytes and exits 0.
It checks the three polynomial certificates and Proposition 8 identities
exactly; the coefficient formula, zero constant/linear terms and rational
excluded-degree witnesses for positive degrees through 60; and numerical
boundary/interior samples through degree 20. The symbolic boundary-reduction
expressions for degrees 3, 5 and 7 are evaluated numerically at the two
parameters used by the script. Those sampled evaluations are not a symbolic
identity proof. No program or dataset is embedded here.

## Triage

### What the settlement shows

| Item | Status and evidence | Exact scope |
| --- | --- | --- |
| Remark 4 degree classification | Proved; kernel-checked `result` | Every positive natural degree and every complex point of the closed disk |
| Boundary defect mechanism | Proved; kernel-checked private `boundary_power` and `boundary_defect` | Every natural degree on $|z-2|=1$ |
| Three positive certificates | Proved; kernel-checked private `positive_D` | $n=5,6,7$ and all real $u\ge1$ |
| Quadratic coefficient | Proved; kernel-checked private `Q_coeff` and `R_coeff` | Every natural degree |
| Negative excluded-degree coefficient and boundary witness | Proved; kernel-checked private `c_negative`, `negative_witness` and `excluded_witness` | Every positive degree outside $\{5,6,7\}$ |
| Excluded degrees fail arbitrarily close to $1$ | Proved in prose below | Every excluded positive degree |
| Proposition 8 factorization identities; finite coefficient/witness checks; numerical samples | Computed by the immutable experiment above; exit 0 and stated SHA-256 | Exact algebra as described above through degree 60; sampled norms through degree 20 |
| Source limit $\min_{z\in B}|(z)_n/z|\to2\pi$ | Open | Not a consequence of the classification |
| Remark 3 bound $|(z)_n|\ge\min(n,2\pi)$ on $B$ | Open | Not settled here |
| Canonical settlement and independent review | Frozen settling declaration and canonical mirror; independent review remains open | The Draft PR standing records the review verdicts |
| Literature completeness | `ASSUMED-UNVERIFIED` | Only the searches recorded in #20656 |

The positive certificates, with $t=u-1$, are

$$
\begin{aligned}
32D_5(1+t)&=t^3(340+160t+31t^2),\\
64D_6(1+t)&=t^2(48+1376t+984t^2+384t^3+63t^4),\\
128D_7(1+t)&=t^3(4704+4592t+2716t^2+896t^3+127t^4).
\end{aligned}
$$

Thus the quadratic coefficient vanishes at five and seven and is positive
at six; the cubic coefficients at five and seven are $340/32$ and
$4704/128$. Their signs explain the degree cutoff. The parameterized
identities and coefficient formula are kernel-checked as specified in the
table; this explanation is not an additional public theorem.

For the local assertion, fix an excluded positive $n$ and any $\varepsilon>0$.
Choose
$0<t<\min(1,1/[4(M_n+1)],2\varepsilon^2)$.
Then $tM_n<1/4$, so
$D_n(1+t)=t^2(c_n+tT_n(t))<0$.
The same boundary point $z(t)$ violates the inequality and satisfies
$|z(t)-1|^2=t/2<\varepsilon^2$.
This proves failure arbitrarily close to $1$ in prose; the Lean theorem
`excluded_witness` states existence, not the arbitrary-neighborhood version.

The degree-five and degree-six conclusions of Proposition 8 survive and
are included in `result`. The classification adds degree seven and sharp
necessity. The proposed limit and Remark 3 retain their separate open status.

## ASSUMED-UNVERIFIED

Literature completeness and the absence of an independently published
settlement beyond the searched sources are unverified. The escape audit
remains unfinished under #20656. Finite computations and sampled minima
supply corroboration within their stated ranges, not proof of the uniform
classification or of either remaining open question.
