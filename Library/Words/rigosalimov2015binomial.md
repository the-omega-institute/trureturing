---
bibkey: rigosalimov2015binomial
authors: Michel Rigo; Pavel Salimov
year: 2015
title: "Another generalization of abelian equivalence: Binomial complexity of infinite words"
doi: 10.1016/j.tcs.2015.07.025
url: https://orbi.uliege.be/handle/2268/178703
claim: "Section 4, Theorem 7 of the author manuscript states that the m-binomial complexity of a Sturmian word is n+1 at every length n for every m at least two; thus second-order binomial equivalence distinguishes its factor contents. Equation (3) defines the weighted-letter statistic S, and Lemma 10 separates distinct length-n Sturmian factors by S modulo n+1 for n at least one; native prefix area is exactly S."
strata_touched:
  - D5/S1/Words/GoldenRecovery/GoldenFactorSecondOrderBinomialRigidity
license: citation-only
triage: anchor
---

# Second-order binomial faithfulness of Sturmian factors

Rigo and Salimov, Theoretical Computer Science 601, 47-57, establish that for
every Sturmian word and every m at least two, the m-binomial complexity at
length n is n+1. Since a Sturmian word has exactly n+1 distinct factors of
length n, its distinct factors cannot be second-order binomially equivalent.
Section 4 of the author manuscript states this as Theorem 7 and proves the
second-order case explicitly. The author-repository record identifies this
manuscript with the cited journal article; the theorem number here refers to
that manuscript, not an independently inspected publisher typesetting.

Equation (3) in Section 4 defines, for a binary word
$u=u_0\cdots u_{n-1}$,

$$
S(u)=\sum_{k=0}^{n-1}(n-k)u_k.
$$

Lemma 10 states that if $n\geq 1$ and $u,v$ are distinct length-$n$ factors
of the same Sturmian word over $\{0,1\}$, then
$S(u)\not\equiv S(v)\pmod{n+1}$. In particular, equality of $S$ determines
the factor at a fixed positive length.

For the native golden factor $W(n,i)$, encode true as $1$ and false as $0$,
so $u_k=1$ exactly when goldenWord$(i+k)$ is true. Its prefix true count
is $R(i,m)=\sum_{k=0}^{m-1}u_k$. The finite-sum correspondence is

$$
A(i,n)=\sum_{m=0}^{n}R(i,m)
=\sum_{m=0}^{n}\sum_{k=0}^{m-1}u_k
=\sum_{k=0}^{n-1}(n-k)u_k=S(u).
$$

The empty prefix contributes zero. Each letter at offset $k<n$ contributes
to exactly the prefix lengths $k+1,\ldots,n$, hence has weight $n-k$.
Thus equality of native prefix areas gives the classical area-injectivity
conclusion of Lemma 10 for golden factors. At $n=0$, Lemma 10 is not used:
the unique word is empty and both sums are zero.

The binomial coefficient of words counts scattered subsequences, with no
adjacency requirement. For a binary word of fixed length n, let r be its true
count, z=n-r its false count, and p its scattered true-before-false count.
The single-letter counts are r and z. The four length-two counts are
r(r-1)/2, z(z-1)/2, p and rz-p for true-true, false-false, true-false and
false-true respectively. Thus equality of (r,p) at fixed length is exactly
second-order binomial equivalence. Relabeling the two letters preserves the
Sturmian theorem.

The repository's golden-factor count recovery and its equivalent profile
kernel statement are this classical faithfulness result for the golden word.
They recover factor contents and do not recover absolute occurrence indices.
The length-zero case is included: the unique word is empty and its profile
is (0,0). No faithfulness for unrestricted binary words is attributed here.

The native definitions, Beatty-coordinate prefix-count comparison, integral
binomial-area identity and representation bridges are repository derivations
connecting the reduced profile to the existing golden-word coordinates.
This attribution makes no novelty claim for the classical area-injectivity
or faithfulness conclusions or for counting and normalization helpers.

## Verified locator

- DOI: https://doi.org/10.1016/j.tcs.2015.07.025
- Author-repository record: https://orbi.uliege.be/handle/2268/178703
- Author manuscript: https://orbi.uliege.be/bitstream/2268/178703/1/binomial_TCS_final.pdf
- Section 4, Theorem 7, manuscript page 6; proof on manuscript page 8.
- Section 4, equation (3) and Lemma 10, manuscript page 7; Lemma 10 proof
  on manuscript pages 7-8. These locators use manuscript numbering, not
  independently inspected publisher numbering.
