---
bibkey: szabo2024primeproducts
authors: Barnabás Szabó
year: 2024
title: On the existence of products of primes in arithmetic progressions
doi: 10.1112/blms.12990
url: https://arxiv.org/pdf/2208.05762v1
claim: Proposition 6 bounds a triangular logarithmically weighted prime-character sum for bounded-order nonprincipal characters; the actual CA application uses all odd exponent layers and retains ramified zeros.
strata_touched: []
license: citation-only
triage: anchor
---

# A signed prime sum that preserves the actual odd layers

The article appeared in *Bulletin of the London Mathematical Society*
**56** (2024), 1227–1243,
[DOI:10.1112/blms.12990](https://doi.org/10.1112/blms.12990).
The inspected primary sources are the [published PDF](https://wrap.warwick.ac.uk/183332/2/WRAP-existence-products-primes-arithmetic-progressions-Szab%C3%B3-2024.pdf),
Proposition 6 and its proof, printed pp.1233–1234, and
[arXiv:2208.05762v1](https://arxiv.org/abs/2208.05762v1), dated 11 August
2022, where Proposition 6 and its proof are on printed p.7. The result is reused
without reproving the analytic estimate. No complete proof audit, effective
error modulus, Lean verification or strongest-available-result claim is made.

For fixed $\alpha>0$, put $f_\alpha(t)=(\alpha-t)_+$ for $t\ge0$.
Proposition 6 gives, as $q\to\infty$, for nonprincipal Dirichlet characters
$\chi\bmod q$ of bounded order,

$$
\operatorname{Re}\sum_p\frac{\chi(p)\log p}{p}
f_\alpha\!\left(\frac{\log p}{\log q}\right)
\le\left(\frac\alpha8+o(1)\right)\log q.
\tag{S1}
$$

The support of the weight is $p\le q^\alpha$. The modulus need not be
prime, cube-free or bounded in its cubic part; the paper's separate
prime-product theorems have their own conditions. Quadratic characters
have the required bounded order two. Primes dividing $q$ have value zero.
No GRH or deletion of an exceptional character is imposed in (S1).

The source applies Heath-Brown's Lemma 5.2 at $s=1$, using the bounded
order parameter $1/4$. Its nonnegative real Laplace transform lets the
zero terms be discarded with the required sign, while higher prime powers
cost $O_\alpha(1)$. These are the source's proof ingredients, not a new
spectral correspondence between finite FIB frequencies and zeta zeros.

The [actual CA application](pollack2017nonresidues.md#all-odd-layers-strengthen-the-signed-character-restriction)
uses (S1) with a triangular weight transported from the scale $P^+(n)$.
It retains the same integer's character, all tied choices and conductor
zeros. It does not infer reciprocal-prime mass or a signed Robin margin
merely from this signed logarithmic weight.
