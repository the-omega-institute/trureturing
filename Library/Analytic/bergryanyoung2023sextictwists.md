---
bibkey: bergryanyoung2023sextictwists
authors: Jennifer Berg; Nathan C. Ryan; Matthew P. Young
year: 2023
title: "Vanishing of Quartic and Sextic Twists of L-functions"
doi: null
url: https://arxiv.org/abs/2301.05329v2
claim: "Corollary 3.23 supplies equidistribution of normalized Gauss-sum squares for totally sextic primitive Dirichlet characters; full-family sextic equidistribution is Conjecture 3.24. The mixed-family discussion does not supply the project's coupled Hecke estimate."
strata_touched: []
license: citation-only
triage: anchor
---

# Composite-even Gauss sums and the totally sextic boundary

The source is [arXiv:2301.05329v2](https://arxiv.org/pdf/2301.05329v2),
updated 23 January 2023. It studies quartic and sextic Dirichlet twists of
elliptic-curve $L$-functions. Definition 3.1, Lemma 3.21, Corollary 3.23,
display (3.42) and Conjecture 3.24 were inspected in the 31-page primary
PDF. Its full proofs have not been independently audited or Lean compiled
here. The statements below are attributed source results and conjectures.

## Proved subfamily and conjectured full family

Definition 3.1 calls a primitive character totally order six when every
prime-power conductor component has exact order six. Corollary 3.23,
attributed to Patterson, states that

$$
\frac{\tau(\chi)^2}{q},\qquad q=\operatorname{cond}(\chi),
$$

is equidistributed on the unit circle in this totally sextic subfamily.
Section 3.1 also cites Patterson's equidistribution of the normalized Gauss
sum itself and twists by a fixed nonzero integer $k$. The twisted phase
$\arg(\tau(\chi)\chi(k))$ is considered only where $(k,q)=1$;
otherwise $\chi(k)=0$ and the phase is undefined. These statements do not
specify uniformity for a growing twist or the project's pair-dependent weights.

For all primitive sextic characters, equidistribution of the squares is
**Conjecture 3.24**. Display (3.42) gives asymptotics for selected sixth-power
moments on conductors $q\equiv1\pmod4$; those moments do not settle every
nonzero Fourier mode required for full-family equidistribution. Thus the
paper's discussion of slower full-family convergence must not be cited as
an unconditional full-family equidistribution theorem. Its elliptic-curve
vanishing asymptotics in Conjecture 1.1 are also conjectural.

## The source already supplies the sextic Gauss factorization

Under Lemma 3.21's hypotheses, write $\chi=\chi_2\chi_3$, with quadratic
$\chi_2$ and cubic $\chi_3$ both of conductor $q$, and take the cubic
parameter $\beta$ from Lemma 3.4, so $\beta\overline\beta=q$. Equation
(3.35), printed pp.21--22, is

$$
\tau(\chi)=\mu(q)\chi_3(2)\,
\tau(\chi_2)\tau(\chi_3)\frac{\overline\beta}{q}.
$$

This is an existing Gauss--Jacobi identity. In this source's Dirichlet
family, multiplying by $\mu(q)$ cancels its displayed conductor sign.
It leaves a coupled quadratic Gauss factor, cubic Gauss factor and angular
factor; it supplies no independence theorem for them.

## Relation to the current contour gap

The project's complementary kernel contains a moving quadratic twist
coupled to a cubic Gauss factor. Its joint estimate must retain these
factors on the same arithmetic realization. Replacing it by separate
quadratic and cubic averages requires an additional correlation estimate;
neither Corollary 3.23 nor Conjecture 3.24 supplies one.

The source's conductor $q$ and $\mu(q)$ are rational-integer data. Their
identification with the original Hecke ratio's conductor ideal, its
Möbius coefficient and fixed bad-prime conventions requires a separate
bridge. In particular, a field or norm substitution cannot be inferred
from the matching order six. The source does not bound the original signed
kernel, establish the order-six residue identity needed for (J), provide
detector length coverage, or imply Robin's inequality or RH.
