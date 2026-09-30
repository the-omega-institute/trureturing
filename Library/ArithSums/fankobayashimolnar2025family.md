---
bibkey: fankobayashimolnar2025family
authors: Steve Fan, Mits Kobayashi, Grant Molnar
year: 2025
title: A family of analogues to the Robin criterion
doi: null
url: https://arxiv.org/abs/2511.02106v1
claim: "Equations (3)–(4) define exactly the increment source b_s and total moment U(s)=c(s). The κ-Robin criterion concerns a different LCM-power σ^[κ]; the pinned version has an extra e^γ in its introductory Lagarias formulas that is absent from section 7."
strata_touched: []
license: citation-only
triage: anchor
---

# Fan–Kobayashi–Molnar 2025: the existing increment source

The pinned source is the author preprint
[A family of analogues to the Robin criterion, arXiv:2511.02106v1](https://arxiv.org/pdf/2511.02106v1),
submitted 3 November 2025. The cited definitions, theorem statements and
sections 3, 7 and 8 were inspected; the full analytic proof and numerical
certificates were not independently verified. No journal-publication claim
or Lean verification is made here.

## Exact identification with the FIB source

The paper's equations (3)–(4), on page 2, define

$$
\sigma_{-1}^{[\kappa]}(n)
=\sum_{d\mid n}\mu(n/d)\sigma_{-1}(d)^\kappa,
\qquad
c(\kappa)=\sum_{n\ge1}\frac{\sigma_{-1}^{[\kappa]}(n)}n,
\qquad \sigma_{-1}(d)=\frac{\sigma(d)}d.
$$

Consequently the existing FIB source is exactly

$$
b_s(n)=\sigma_{-1}^{[s]}(n),\qquad U(s)=c(s).
$$

Indeed the multiplicative function on the right has local values

$$
b_s(p^a)=Z(p^a)^s-Z(p^{a-1})^s\quad(a\ge1),
\qquad b_s(1)=1,
$$

with $Z(n)=\sigma(n)/n$. These are the project's local increments.
This identifies an existing arithmetic object, rather than a new source
introduced by the FIB presentation. The common-integer, progression,
low-loss-divisor or complementary-source conditions used later in the
project are additional obligations; the naming match does not supply them.

For fixed $s>0$, the nonnegative divisor expansion also gives the already
used finite relation

$$
\sum_{n\le X}Z(n)^s
=\sum_{d\le X}b_s(d)\lfloor X/d\rfloor\le XU(s).
$$

This finite relation is a direct application of the source expansion, not
an assertion that a fixed-moment asymptotic is uniform in a growing $s$.

## The distinct κ-Robin object and its quantifiers

Definition 1.2 defines a different function

$$
\sigma^{[\kappa]}(n)=\sum_{d\mid n}\mu(n/d)\sigma(d)^\kappa.
$$

For integral $k$, it is the sum of $d_1\cdots d_k$ over ordered tuples
whose least common multiple is $n$. In particular $\sigma^{[1]}(n)=n$;
it is not the ordinary divisor-sum function $\sigma(n)$.
One must not substitute $b_s$ for $\sigma^{[s]}$ in the following theorem.

Theorem 1.5, page 3, states: for each fixed real $\kappa>3/2$, RH is
equivalent to the existence of $N(\kappa)$ such that every integer
$n\ge N(\kappa)$ satisfies

$$
\sigma^{[\kappa]}(n)
<\frac{(e^\gamma n\log\log n)^\kappa}{\zeta(\kappa)}.
$$

For $\kappa\ge2$, the eventual condition can be replaced by this inequality
for every $n>2162160$. This is a reported RH equivalence, not an
unconditional proof of those inequalities or of RH.

Theorem 1.4 states, for each real $\kappa>1$,

$$
\limsup_{n\to\infty}
\frac{\zeta(\kappa)\sigma^{[\kappa]}(n)}
{(e^\gamma n\log\log n)^\kappa}=1.
$$

## Fixed moments do not settle the required growing-parameter error

Proposition 3.1 cites Balakrishnan–Pétermann (1996), Corollary 1, for a
mean-value expansion of $\sigma(n)^\kappa$ with leading coefficient
$c(\kappa)/(\kappa+1)$. Theorem 1.3 / Theorem 3.2 gives

$$
\sum_{n\le x}\sigma^{[\kappa]}(n)
=\frac{c(\kappa)}{(\kappa+1)\zeta(\kappa+1)}x^{\kappa+1}
+O_\kappa\bigl(x^\kappa(\log x)^\kappa\bigr),\qquad \kappa>1.
$$

Here the subscript makes explicit the fixed-parameter reading; the paper
prints $O$ without a subscript and supplies no growing-$\kappa$ range for
this statement. Its Selberg–Delange formulation, Proposition 3.4, cites
Tenenbaum, Theorem II.5.2, and explicitly allows a constant
$c_1=c_1(\alpha,M,c_0)$. It does not independently certify the error required
when $s=y\log y$ in the FIB argument.

The existing Weingartner source card already records the large-positive-
moment expansion for $W(s)$, the moment product of $n/\varphi(n)$, at
$s=y\log y$. That is a different product. Its error must be connected to
$U(s)$ by an actual estimate, rather than replacing $W$ by $U$ in the
cited theorem. This card makes no claim that a uniform theorem for $U$
is absent from the wider literature.

The older Balakrishnan–Pétermann article has DOI
[10.4064/aa-75-1-39-69](https://doi.org/10.4064/aa-75-1-39-69), and Crossref
also indexes an erratum,
[10.4064/aa-87-3-287-289](https://doi.org/10.4064/aa-87-3-287-289).
Those two original texts have not been inspected here; a direct reuse of
their general theorem still requires checking both texts and the parameter
range. The citation through the 2025 paper is not that check.

Section 8, pages 41–42, explicitly proposes studying
$\sigma_{-1}^{[\kappa]}$ and its Robin analogues. It records, for fixed
$\kappa>1$, the asserted maximal-order relation

$$
\limsup_{n\to\infty}
\frac{n\sigma_{-1}^{[\kappa]}(n)}
{\kappa^{\omega(n)}(e^\gamma\log\log n)^{\kappa-1}}=1.
$$

The authors introduce this with “It is not hard to show” without supplying
a full proof at that location. It is a source statement to check before
reuse, not a verified growing-$\kappa$ estimate. Section 8 also cites the
Luca–Pomerance–Solé corrected exceptional-set bound and asks for
$\kappa$-analogues; it gives no improved quantitative count there.

## Introductory Lagarias formulas disagree with the body

The pinned PDF's equation (8) and Theorem 1.7, page 3, contain

$$
H_n+e^\gamma e^{H_n}\log H_n.
$$

The arXiv TeX source `LCMPaperArXiv.tex` contains the same extra factor;
this is not a PDF text-extraction artifact. Reference [8], Lagarias (2002),
Theorem 1.1, instead uses $H_n+e^{H_n}\log H_n$.

The same 2025 paper's section 7 uses the expression without the extra
$e^\gamma$. Specifically, Theorem 7.2, equations (70)–(71), reports for
$\kappa\ge2$ equivalences with the strong and weak inequalities for
$n>55440$; the weak right-hand side is

$$
\frac{(H_n+e^{H_n}\log H_n)^\kappa}{\zeta(\kappa)}.
$$

Corollary 7.4, equation (72), reports this same corrected-form expression
for every $n>1$ when $\kappa\ge3.89$. Theorem 7.5 reports the eventual
version for $\kappa>3/2$. These are exact locations of the discrepancy,
not a silent repair of Theorem 1.7 or a new proof of the body statements.
The erroneous introductory formula is not used as a premise here.

## Original-source locators

- [Pinned abstract](https://arxiv.org/abs/2511.02106v1).
- [Pinned PDF](https://arxiv.org/pdf/2511.02106v1): equations (3)–(4), page 2;
  Theorem 1.5, page 3; Proposition 3.1, page 6; Proposition 3.4, page 9;
  section 7, pages 39–41; section 8, pages 41–42.
- [Pinned arXiv source](https://arxiv.org/src/2511.02106v1):
  `LCMPaperArXiv.tex`.
- [Lagarias original author version](https://arxiv.org/pdf/math/0008177):
  Problem E, equation (1.1), and Theorem 1.1.
