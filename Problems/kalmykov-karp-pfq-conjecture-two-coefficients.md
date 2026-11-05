---
slug: kalmykov-karp-pfq-conjecture-two-coefficients
bibkey: kalmykovkarp2017pfq
doi: 10.1007/s10476-017-0503-z
url: https://arxiv.org/abs/1611.06724
triage: theorem
motivation_gids:
  - D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.claim
  - D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.result
---

# Coefficients of the two-block hypergeometric Turanian

## Problem

S. I. Kalmykov and D. B. Karp, *Log-concavity and Turán-type inequalities
for the generalized hypergeometric function*, arXiv:1611.06724v1, Section 3,
page 6:

> Conjecture 2. Suppose p1 ≤ q1 , p2 ≤ q2 and conditions (13) hold for a1 , b1 and a2 , b2 . Then the function µ → f (µ; x) defined in (3) is log-concave on [1, ∞) and the corresponding generalized Turánian ∆f (α, β; x) has nonnegative coefficients at all powers of x.

The standing assumption on page 2 is:

> We will always assume that a2 is not empty (i.e. p2 ≥ 1), while all other subvectors are allowed to be empty.

For positive parameter vectors in two blocks, equation (3) defines

$$
f(\mu;x)=\frac{\Gamma(\mathbf a_2+\mu)}{\Gamma(\mathbf b_2+\mu)}
\,{}_pF_q(\mathbf a_1,\mathbf a_2+\mu;
\mathbf b_1,\mathbf b_2+\mu;x).
$$

Here a Gamma value at a vector means the product over its entries. Writing
$(a)_n$ for the rising factorial and $c(t)$ for the shifted Gamma product
ratio, the Taylor coefficient is

$$
F_n(\mu)=
\frac{\prod_i(a_{1,i})_n}{\prod_j(b_{1,j})_n}
\frac{c(\mu+n)}{n!},\qquad
c(t)=\frac{\prod_i\Gamma(a_{2,i}+t)}{\prod_j\Gamma(b_{2,j}+t)}.
$$

Equation (2) defines

$$
\Delta_f(\alpha,\beta;x)=
f(\mu+\alpha;x)f(\mu+\beta;x)
-f(\mu;x)f(\mu+\alpha+\beta;x),
$$

whose degree-$m$ coefficient is

$$
\delta_m=\sum_{k=0}^m
\bigl[F_k(\mu+\alpha)F_{m-k}(\mu+\beta)
-F_k(\mu)F_{m-k}(\mu+\alpha+\beta)\bigr].
$$

For each block separately, condition (13) is

$$
\frac{e_{q-j}(\mathbf b)}{e_{p-j}(\mathbf a)}
\le\frac{e_{q-j-1}(\mathbf b)}{e_{p-j-1}(\mathbf a)}
\qquad(0\le j<p),
$$

with $e_0=1$. The coefficient clause quantifies over $p_1\le q_1$,
$1\le p_2\le q_2$, all four positive vectors satisfying their respective
chains, every $\mu\ge1$, all $\alpha,\beta\ge0$, and every natural degree $m$.

Formal correspondence. All Lean names below have prefix
`D5.S3.Analytic.HypergeometricShiftTuran`.

| Source object | Lean name | Correspondence |
| --- | --- | --- |
| Unshifted rising factorial ratio | `TwoBlockResult.pochRatio` | Products of `(ascPochhammer ℝ n).eval` at the unshifted parameters. |
| Equation (3) Taylor coefficient | `TwoBlockResult.seriesCoeff` | Rising factorial ratio times `Defs.coeff` for the shifted block at $\mu+n$, divided by $n!$. |
| Equation (2) Cauchy coefficient | `TwoBlockResult.twoBlockTuranCoeff` | Exact finite sum with the factorials contained in `seriesCoeff`. |
| Shifted Gamma ratio and condition (13) | `Defs.coeff`, `Defs.esymm`, `Defs.cond13` | Reused definitions, with the ratio chain imposed separately on both blocks. |
| Conjecture 2 coefficient clause | `TwoBlockResult.claim` | All dimensions, positivity assumptions, both chains, nonempty shifted numerator, shifts and coefficient degrees. |
| Negative coefficient family | `TwoBlockResult.half_parameter_family_neg` | Empty unshifted blocks, shifted numerator $(1)$, repeated half denominators, $\mu=1$, $\alpha=\beta=1/2$, and every $q\ge7$. |
| Refutation | `TwoBlockResult.result` | Exactly $\neg\,\texttt{TwoBlockResult.claim}$. |

## Motivation

A negative coefficient under all of the stated hypotheses refutes the
coefficient clause. Conjecture 2 requires the shifted numerator to be
nonempty, so a counterexample with no shifted numerator does not meet its
hypotheses. The witness here retains the shifted numerator $(1)$.

## Gap

The explicit calculation in Route refutes the coefficient clause. The D5
modules of this delivery compile in the repository CI and encode the family
inequality and its specialization at $q=7$.
The separate assertion of log-concavity at a fixed nonnegative $x$ is not
settled here.

## Route

Take $\mathbf a_1=\mathbf b_1=()$, $\mathbf a_2=(1)$,
$\mathbf b_2=(1/2,\ldots,1/2)\in\mathbb R^q$, $\mu=1$,
$\alpha=\beta=1/2$, and $m=1$. The empty rising factorial products equal
one, so the coefficient reduces to `Defs.turanCoeff` for the shifted block.
Now

$$
c(t)=\frac{\Gamma(1+t)}{\Gamma(1/2+t)^q},\qquad
\delta_1=2c(3/2)c(5/2)-c(2)^2-c(1)c(3).
$$

The integer and half-integer Gamma identities give

$$
\begin{aligned}
c(3/2)&=\Gamma(5/2),&
c(5/2)&=\Gamma(7/2)2^{-q},\\
c(2)&=2\Gamma(5/2)^{-q},&
c(1)&=\Gamma(3/2)^{-q},&
c(3)&=6\Gamma(7/2)^{-q},
\end{aligned}
$$

where $\Gamma(3/2)=\sqrt\pi/2$, $\Gamma(5/2)=3\sqrt\pi/4$ and
$\Gamma(7/2)=15\sqrt\pi/8$. Consequently

$$
\delta_1=\frac{45\pi}{16}\,2^{-q}
-4\left(\frac{16}{9\pi}\right)^q
-6\left(\frac{16}{15\pi}\right)^q.
$$

The bound $\pi<3.15$ gives $32/(9\pi)>640/567>1$. Exact rational
arithmetic gives $(640/567)^7>45\cdot3.15/64$, and monotonicity in the
natural exponent gives

$$
\left(\frac{32}{9\pi}\right)^q>
\frac{45\pi}{64}\qquad(q\ge7).
$$

Multiplying by $4\cdot2^{-q}>0$ shows that the middle term in the closed
form exceeds its positive leading term. The final subtracted term is
strictly positive, so $\delta_1<0$ for every $q\ge7$.

The first block's chain is vacuous. In the shifted block, $p_2=1$ and
$e_1(\mathbf a_2)=e_0(\mathbf a_2)=1$. Since the symmetric function of
$q$ repeated entries $x$ in degree $k$ is $\binom qk x^k$, the only chain
inequality is

$$
2^{-q}\le q\,2^{1-q},
$$

which holds for $q\ge1$. At $q=7$ all dimension, positivity and shift
requirements are satisfied, contradicting coefficient nonnegativity.

## Falsifier

A source requirement that either unshifted block be nonempty would invalidate
this correspondence; the printed standing assumption expressly permits both
to be empty. The calculation contains both degree-one Cauchy summands, the shifted
numerator Gamma factors and all factorials. Condition (13) for the shifted
block is checked explicitly. The claim retains all coefficient degrees and
both chains. The D5 modules of this delivery compile in the repository CI.

## Evidence

The source is arXiv:1611.06724v1, pages 2 and 6, equations (2), (3), (13)
and Conjecture 2; journal publication *Analysis Mathematica* 43 (2017),
567–580, DOI 10.1007/s10476-017-0503-z. The Lean source is
`D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.lean`.
`TwoBlockResult.result` is written with type exactly `¬ TwoBlockResult.claim`.
The D5 modules of this delivery compile in the repository CI.

The orchestrator-reported literature scope comprises all 15 OpenAlex citing
works, arXiv and general web search, and repository search for the source
identifier. No settlement of Conjecture 2 was found in that scope. Sokal's arXiv:2204.01045 concerns
Conjecture 3. These source and literature findings are orchestrator-reported,
and do not certify priority or exhaustive coverage.

The numerical entry uses the driver in
[the-omega-institute/trureturing-experiments at revision ccf77c1917e9d1a2f3d101bcd815841d9ca7dcb1](https://github.com/the-omega-institute/trureturing-experiments/tree/ccf77c1917e9d1a2f3d101bcd815841d9ca7dcb1/experiments/kalmykov-karp-pfq-turanian):
`experiments/kalmykov-karp-pfq-turanian/two_block_scan.py`, sha256
`1a009ce42782cc93ea7bb3d21c4c154c1c4f6336dd1bed57790b6f6822e9c07d`,
with `common.py`, sha256
`99d8d5329e2fd15025ebf1f46f67bbfa245787a2628075c93c10b48a98c5d2d2`.
Command: `python3 two_block_scan.py`, run from that directory with Python
3.12 and mpmath 1.4.1, exit 0. At 40 decimal digits, for
$q=1,\ldots,11$ the closed form equals the direct Cauchy sum to a maximum
absolute discrepancy of $4.6\cdot10^{-41}$. The shifted numerator is
$[1]$, the denominator is $[1/2]^q$, $\mu=1$, $\alpha=\beta=1/2$ and
the degree is one. The first coefficient is approximately $0.01693$ at
$q=5$, $-0.002483$ at $q=6$ and $-0.008420$ at $q=7$.

## Triage

### What the settlement shows

The failure mechanism is the exponential dependence on denominator
multiplicity. In the degree-one coefficient, the negative balanced product
$c(2)^2$ eventually dominates the positive product
$2c(3/2)c(5/2)$. A nonempty shifted numerator contributes the fixed factors
$45\pi/16$, $4$ and $6$ in the closed form, and the exponential dominance
persists. Thus neither $\mu\ge1$ nor the two ratio chains prevent this
failure when both shifts are $1/2$.

- **PROVED IN PROSE (Route):** the closed form above and its strict
  negativity for every $q\ge7$, with all source hypotheses satisfied at
  $q=7$, refute the coefficient clause. The D5 argument is
  `TwoBlockResult.half_parameter_family_neg` followed by
  `TwoBlockResult.result`; the D5 modules of this delivery compile in the
  repository CI.
- **COMPUTED:** `python3 two_block_scan.py`, exit 0, in
  `experiments/kalmykov-karp-pfq-turanian` of
  `the-omega-institute/trureturing-experiments` at revision
  `ccf77c1917e9d1a2f3d101bcd815841d9ca7dcb1`, driver sha256
  `1a009ce42782cc93ea7bb3d21c4c154c1c4f6336dd1bed57790b6f6822e9c07d`
  (`common.py` sha256
  `99d8d5329e2fd15025ebf1f46f67bbfa245787a2628075c93c10b48a98c5d2d2`),
  Python 3.12 and mpmath 1.4.1: for $q=1,\ldots,11$ the closed form
  equals the direct sum with maximum discrepancy $4.6\cdot10^{-41}$
  at 40 digits. The first coefficient is approximately $0.01693$ at
  $q=5$, $-0.002483$ at $q=6$ and $-0.008420$ at $q=7$. Thus the proved
  sufficient threshold $q\ge7$ is not claimed to be sharp.
- **PROVED in the source, not formalized here:** Theorem 3's integer-shift
  conclusions remain unaffected by this witness. With empty unshifted
  blocks the series is equation (10), and the shifts used here are
  noninteger. The counterexample does not invalidate an already proved
  statement restricted to integer shifts.
- **OPEN:** the sign of the full Turanian and the log-concavity clause of
  Conjecture 2 for this family at a fixed $x\ge0$; a classification of the
  parameter ranges where coefficient nonnegativity holds; and whether a
  lower bound on $\mu$ depending on denominator multiplicity restores it.
  Conjectures 1 and 2 have different stated domains, so their coefficient
  clauses require their respective witnesses. The source's proved results
  retain their hypotheses; an extension relying on Conjecture 2's full
  coefficient assertion cannot use that assertion after this refutation.

## ASSUMED-UNVERIFIED

Axiom closure and Reg compilation: not recorded here. Emitted Blueprints
and the four-slot registration's binding evidence: not recorded here. The
source and literature checks are supplied by the orchestrator; exhaustive literature coverage, citation-index completeness
and priority are unverified. Numerical agreement and signs are finite
multiprecision observations rather than proofs of a uniform statement. No
claim about the sign of the full Turanian or log-concavity at a fixed $x$
follows solely from the negative coefficient.
Four-slot escape registrations of the shared public Gamma and power helpers (and, for the two-block module, of `first_coefficient_eq`) are not completed; the gap is recorded at https://github.com/the-omega-institute/trureturing/issues/20966.
