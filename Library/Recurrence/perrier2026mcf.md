---
bibkey: perrier2026mcf
authors: Rachel Perrier
year: 2026
title: Multidimensional Continued Fractions and Riordan Arrays
doi: 10.54550/ECA2026V6S4R33
url: https://ecajournal.haifa.ac.il/Volume2026/ECA2026_S4R33.pdf
claim: "Section 5, printed pp. 14-15: We conjecture that solving these recurrences yields the displayed rational functions R_1 and R_k; shifted generating functions are defined on printed pp. 8 and 12."
strata_touched:
  - D5/S1/Recurrence/Algebraic/PerrierPeriodicGeneratingFunctions
license: citation-only
triage: anchor
---

# Perrier's period-one generating functions

Rachel Perrier, *Multidimensional Continued Fractions and Riordan Arrays*,
Enumerative Combinatorics and Applications 6:4 (2026),
DOI [10.54550/ECA2026V6S4R33](https://doi.org/10.54550/ECA2026V6S4R33).
The PDF footer prints Article #S2R33; the DOI and filename use S4R33.

## Verified locator

DOI: 10.54550/ECA2026V6S4R33
Source URL: https://ecajournal.haifa.ac.il/Volume2026/ECA2026_S4R33.pdf
Section 5, printed pp. 14-15, gives the initial vector, the period-one
recurrences, and the two conjectured rational functions. Printed pp. 8
and 12 define the shifted generating functions. The quotations below
retain those source sentences and equations.

## Source statement

Printed p. 14: “The same method extends to higher dimensions.”
The period-one paragraph states:

> Assume period 1, so $m_{j,i}=m_j$ for $1 \le j \le k-1$ and $i \ge 0$. With initial values
> $\lambda_{-1}=1$, $\lambda_0=a_{k-1}$, $r_1^{(-1)}=1$, $r_2^{(-1)}=a_1$, $\ldots$, $r_k^{(-1)}=a_{k-1}$,
> we obtain

The coordinate recurrence continues on printed p. 15:

$$
r_1^{(n+1)}=r_k^{(n)},\qquad
r_{j+1}^{(n+1)}=r_j^{(n)}+m_jr_k^{(n)},\qquad 1\le j\le k-1.
$$

> We conjecture that solving these recurrences yields

$$
R_1(t)=\frac{(a_1-m_1)t^{k-1}+(a_2-m_2)t^{k-2}+\cdots+(a_{k-1}-m_{k-1})t+1}
{1-m_{k-1}t-m_{k-2}t^2-\cdots-m_1t^{k-1}-t^k}
$$

> and

$$
R_k(t)=\frac{t^{k-1}+a_1t^{k-2}+\cdots+a_{k-2}t+a_{k-1}}
{1-m_{k-1}t-m_{k-2}t^2-\cdots-m_1t^{k-1}-t^k}.
$$

Printed p. 8:

> To retain the stated initial values, define the shifted generating functions

$$
R_1(t)=\sum_{n\ge0}r_1^{(n-1)}t^n,\qquad
R_2(t)=\sum_{n\ge0}r_2^{(n-1)}t^n.
$$

Printed p. 12:

> Define the shifted generating functions

$$
R_i(t)=\sum_{n\ge0}r_i^{(n-1)}t^n,\qquad i=1,2,3.
$$

## Encoding and scope

Set $k=d+1$. Lean coordinate $j$ represents source coordinate $j+1$;
Lean time $n$ represents source time $n-1$. The parameter functions
$m,a:\operatorname{Fin}(d)\to K$ use the same zero-based shift.
`Recurrence` is the four-clause predicate containing the initial vector
and both next-vector equations. These recursively determine a unique
solution for every parameter pair. `R` is literally `PowerSeries.mk`
of the corresponding coefficient sequence. `D`, `P`, and `Q` are the
displayed finite sums, with constants embedded by `PowerSeries.C`.
The conclusion concerns every solution, over every commutative ring and every
natural $d$, including the empty case $d=0$:
`R r 0 * D m = P m a ∧ R r (Fin.last d) * D m = Q a`.

Section 5 states the recurrence and conjectured formulas without naming a
coefficient domain. The paper's ambient construction is integral: the companion
matrices have 'nonnegative integer entries' (printed p. 7), and the period
parameter is $k \in \mathbb{Z}_{>0}$ in the two-dimensional section and
$k \in \mathbb{Z}$ in the three-dimensional section. The formal statement over
an arbitrary commutative ring directly includes $\mathbb{Z}$; a statement over
an arbitrary field cannot be instantiated at $\mathbb{Z}$. Since the constant
term of `D m` is one, `D m` is a unit in the formal power-series ring. The
multiplicative conclusion is therefore equivalent to the printed quotients.
The preregistration and domain correction are recorded in
https://github.com/the-omega-institute/trureturing/issues/8627.

Section 5 does not repeat the definition of $R_j$ for general $k$.
Retaining the shifted convention of pp. 8 and 12 is the contextual reading
of “The same method extends to higher dimensions.” The following sentence,
“We further conjecture that these recurrences produce generating functions
for the generalized recurrence in equation (7).”, is outside this result.

The author's 2023 Washington State University thesis, cited as reference
[22], was not retrieved. Whether it already proves the general case is
ASSUMED-UNVERIFIED. The article itself states the general formulas as a
conjecture; its two- and three-dimensional cases are already proved there.
