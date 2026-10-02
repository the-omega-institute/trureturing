---
bibkey: lucapomerancesole2025robin
authors: Florian Luca, Carl Pomerance, Patrick Solé
year: 2025
title: "Correction to: On Robin's inequality"
doi: null
url: https://math.dartmouth.edu/~carlp/robin4.pdf
claim: Robin violations have global counting function at most exp(O(log x / log log x)); this does not supply a per-progression singleton theorem or exclude a remaining candidate.
strata_touched: []
license: citation-only
triage: anchor
---

# Correction to: On Robin's inequality

The inspected source is the four-page [author-hosted correction](https://math.dartmouth.edu/~carlp/robin4.pdf), linked from [Carl Pomerance's publication list](https://math.dartmouth.edu/~carlp/) as *Integers*, A8 (Corrigendum, 2025). Its header has unfilled editorial date fields; the year and publication description here follow that author list. The original paper is Luca–Solé, *Integers* 25 (2025), A8. The correction explicitly identifies an oversight in its proof of the earlier subpower counting claim and replaces that argument with a stronger explicit estimate. This card uses the corrected argument.

## Corrected global counting theorem

Write

$$
\mathcal N_R(x)=\{5040<n\le x:\sigma(n)\ge e^\gamma n\log\log n\}.
$$

Theorem 1 gives

$$
\#\mathcal N_R(x)\le\exp\!\left(O\!\left(\frac{\log x}{\log\log x}\right)\right).
$$

The weak inequality in the definition includes equality at Robin's boundary. Lemma 1 shows that, for sufficiently large $x$, a violation in $(x/2,x]$ has

$$
\omega(n)>\frac{\log x}{\log\log x},
$$

where $\omega$ counts distinct prime divisors. The proof combines the Euler-product bound for $\sigma(n)/n$, a strong Mertens estimate and the expansion of the $k$th prime. The counting step uses Pomerance, “On the distribution of round numbers,” *Lecture Notes in Mathematics* 1122 (1985), Theorem 6.1. That older theorem is cited through the inspected correction; this card does not claim a fresh inspection of its full original proof.

The last section also notes that a violation of the Lagarias inequality, for sufficiently large $n$, violates Robin: the Lagarias right-hand side exceeds $e^\gamma n\log\log n$ by a positive term of order $n/\log n$. Its exceptional set therefore inherits the same asymptotic counting bound. This is a comparison of necessary conditions on failures, not an equivalence between the two pointwise failure predicates.

## Comparison with the FIB source estimates

The FIB theory's divisor-increment source uses

$$
w_s(d)=b_s(d)/d,\qquad
J_s(d)=\log\bigl(\max_e w_s(e)/w_s(d)\bigr).
$$

The low-loss height estimate and the common-divisor argument in [the theory volume](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md) localize possible exceptional integers in a prescribed growing reduced residue class. For the actual family $N_g=1+F_r g$, the integer relation is preserved throughout. A reference $n_\circ$ and two actual low-loss divisors give the common factor

$$
q_0=\frac{n_\circ}{\operatorname{lcm}(v_1,v_2)},\qquad
v_i=\frac{n_\circ}{\gcd(n_\circ,d_i)}.
$$

Its size can force the two integer locations to coincide. The complementary positive moment estimate additionally bounds the total weighted contribution outside that location. Neither step excludes the remaining integer.

Global sparsity at the scale displayed in Theorem 1 is established prior work. The inspected correction does not state uniqueness in every specified growing reduced residue class, nor the increment-source complementary moment bound. Conversely, the FIB-window result does not cover arbitrary integers and cannot replace the global theorem. A bounded comparison with this source does not establish originality of the more local result.

Finite interval experiments for one FIB window are method certificates, not a new record of Robin verification. For example, the index $r=5{,}000{,}011$ used by the current source computation has $\log X<4{,}812{,}126$. It lies far below the already published finite verification range recorded in the [Hertlein note](../notes/hertlein2018robin.md). No extension of that published range, no Lean verification of the new analytic arguments, and no RH resolution is claimed here.
