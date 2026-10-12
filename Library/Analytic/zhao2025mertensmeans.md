---
bibkey: zhao2025mertensmeans
authors: Tianyu Zhao
year: 2025
title: On the mean values of the error terms in Mertens' theorems
doi: 10.1007/s40993-025-00640-y
url: https://arxiv.org/abs/2411.18903v2
claim: The paper supplies an RH criterion through cumulative linear Mertens errors and an exact Chebyshev tail identity; transport to the Robin kernel retains a signed future mean that is not controlled at the selected arithmetic wells.
strata_touched: []
license: citation-only
triage: anchor
---

# Cumulative Mertens errors and the actual Robin tail

The inspected primary is [arXiv:2411.18903v2](https://arxiv.org/pdf/2411.18903v2),
revised 24 June 2025, 23 pages, 566,342 bytes, SHA-256
`db20602b1b53c56b06ccdb5b6e72f848ad804d27e6b5c1809f265af0d4b240b1`.
Crossref records the DOI above in *Research in Number Theory* 11(3),
article 62, with publication date 16 June 2025. The journal edition was
not inspected; the locators below refer to the accepted arXiv version.
This note applies existing identities, without repeating their proofs,
finite computations, or claiming a new theorem or Lean certification.

## The existing criterion and its hypotheses

The definitions on printed p.1 are

$$
\mathcal E_1=-\gamma-\sum_p\sum_{j\ge2}\frac{\log p}{p^j},\qquad
E_1(x)=\sum_{p\le x}\frac{\log p}{p}-\log x-\mathcal E_1,
$$

and $E_2(x)=\sum_{p\le x}1/p-\log\log x-\mathcal E_2$, with
$\mathcal E_2=\gamma-\sum_p\sum_{j\ge2}1/(jp^j)$.
Theorem 1, printed p.2, states, separately for each $i\in\{1,2\}$,

$$
\mathrm{RH}\quad\Longleftrightarrow\quad
\int_2^X E_i(t)\,dt>0\quad\text{for every real }X>2.
$$

Theorem 2's analogous discussion of the nonlinear product error $E_3$
has an additional boundary: if
$\Theta=\sup\{\Re\rho:\zeta(\rho)=0\}=1$, its sign-change conclusion
assumes Assumption 1. That assumption must not be dropped when citing
the nonlinear criterion. Corollary 1, printed p.3, assumes RH and
$0<c<[(2-B_1)/(2+B_1)]^2$, where $B_1=2+\gamma-\log(4\pi)$,
for its positive averages on $[cX,X]$ and an eventual cutoff depending on $c$.
None is an unconditional estimate at a selected Robin source.

## Use the existing tail identity at the same cutoff

Put $F_1(X)=\int_2^X E_1(t)\,dt$ and
$c_1=2\log2-2+2\mathcal E_1$.
Equation (14), printed p.6, gives directly

$$
Q_\theta(X):=\int_X^\infty\frac{\theta(t)-t}{t^2}\,dt
=\frac{c_1-F_1(X)}{X}.
\tag{Z1}
$$

The paper derives this using the Rosser--Schoenfeld partial-summation
identity cited there. Both the identity and that proof are reused.
At an actual integer in the
[joint regular source class](../Arith/caveney2012sacaga.md#restrict-the-unpaid-signed-estimate-to-this-joint-source-class),
the substitution is $X=A=\log N$, not $X=N$ or the largest prime
factor of $N$. The endpoint relation for $\theta(A)$ does not supply
the cumulative value $F_1(A)$.

For the existing Robin kernel, retain

$$
r(t)=\frac{1+\log t}{\log^2t},\qquad
k(t)=\frac{r(t)}{t^2},\qquad
r'(t)=-\frac{\log t+2}{t\log^3t},
$$

and every higher-prime-power contribution

$$
H_2(A)=\int_A^\infty[\psi(t)-\theta(t)]k(t)\,dt.
$$

Applying finite partial integration to (Z1), then using the
[existing unconditional convergence supplier](../Weil/johnstonyang2022pnt.md)
at the infinite endpoint, gives the same full signed tail

$$
I_\psi(A)=H_2(A)
+r(A)\frac{c_1-F_1(A)}A
+\int_A^\infty r'(t)\frac{c_1-F_1(t)}t\,dt.
\tag{Z2}
$$

This is an application with its weighted remainder retained, not a new
criterion or a signed-tail estimate. In particular, dropping the last
integral is not the transport from $t^{-2}$ to $k(t)$.

## A small measure does not bound the future signed mean

Write $L=\log A$, $T=\sqrt A\,L$ and
$m(t)=[F_1(t)-c_1]/\sqrt t$. Define the positive finite measure

$$
d\nu_A(t)=\frac{\sqrt A\,L(\log t+2)}{t^{3/2}\log^3t}\,dt,
\qquad t\ge A.
$$

Then (Z2) reads exactly

$$
T I_\psi(A)=T H_2(A)
-\left(1+\frac1L\right)m(A)+\int_A^\infty m(t)\,d\nu_A(t).
\tag{Z3}
$$

The change $t=Ae^u$ gives

$$
\nu_A([A,\infty))
=L\int_0^\infty e^{-u/2}\frac{L+u+2}{(L+u)^3}\,du
\le\frac2L+\frac4{L^2}.
$$

The measure's mass tends to zero, but no uniform bound for the
normalized mean $m$ on its infinite support has been supplied.
Small mass therefore does not justify discarding its signed integral.
Nor can the positive-means conclusion of Theorem 1 be imported
without its RH premise.

The original eventual floor $T I_\psi(A)\ge-M$ requires the upper
comparison

$$
\left(1+\frac1L\right)m(A)-\int_A^\infty m(t)\,d\nu_A(t)
\le T H_2(A)+M
\tag{Z4}
$$

at every sufficiently large actual source in the same joint class.
The [existing prime-power and core estimates](../ArithSums/nicolas2025comparison.md#the-endpoint-condition-at-actual-self-tangent-sources)
are reused; they do not control the left side of (Z4).
Theorem 1 and its window corollary have no CA, neutral-band or
right-tail-maximality condition providing this comparison.
This identifies a cumulative ordinary-prime quantity for further
research while preserving the full original tail and its unpaid sign.
