# Reconstructing a nonhomogeneous legal binary chain

## Abstract

Strictly interior site means determine a normalized hard-core binary path law, and this law is unique among first-order Markov laws with those means.

A word is a Boolean function on a finite interval. The predicate Adm requires that no two consecutive positions are both true. Indices start at zero. The parameter n describes a path with n+2 sites, so every path of length at least two occurs. A function u on the natural numbers supplies the site means; only its first n+2 values are used. Interior u N requires every used mean to lie strictly between zero and one and every adjacent empty-empty remainder to be positive.

The table site(u) assigns mass 1-u to false and u to true. In the order false, true, the four entries of pair(u,v) are 1-u-v, v, u, and zero. The transition step(u,v,a,b) divides the pair entry by site(u,a). Strict interiority makes both denominators positive. Every transition row sums to one, and propagating site(u) through this transition gives site(v). The transitions can differ at every position.

The function chain(q,K,m) assigns a word its initial mass q followed by the product of its m transition entries. The function completion(u,n) instead multiplies all n+1 adjacent pair entries and divides by the product of the n internal site entries. The denominator removes the second occurrence of each internal site. There is no endpoint denominator. For n=0 the internal product is empty and equals one.

LegalLaw m P means that P is nonnegative, sums to one over all Boolean words of length m+1, and vanishes outside Adm. Means u m P requires the probability of true at each position i to equal u(i). The cylinder mass is the sum of P over words with an exact given initial segment. Markov m P requires nonnegative stochastic rows such that extending any history by a bit multiplies its cylinder mass by the row entry at its last bit. On a history of positive probability this entry is precisely the conditional probability of the next bit. The equation also includes histories of zero probability. Rows after the end of the path are unrestricted.

**Theorem 1.1 (Existence, prescribed means, and uniqueness).**

$$\forall u \in \mathbb{N} \to \mathbb{R},\; \forall n \in \mathbb{N},\; \mathrm{Interior}\left(u, n + 2\right) \Rightarrow \left(\mathrm{LegalLaw}\left(n + 1, \mathrm{completion}\left(u, n\right)\right) \land \left(\mathrm{Means}\left(u, n + 1, \mathrm{completion}\left(u, n\right)\right) \land \left(\mathrm{Markov}\left(n + 1, \mathrm{completion}\left(u, n\right)\right) \land \left(\forall P \in \left(\mathrm{Fin}\left(n + 2\right) \to \mathrm{Bool}\right) \to \mathbb{R},\; \mathrm{LegalLaw}\left(n + 1, P\right) \Rightarrow \left(\mathrm{Means}\left(u, n + 1, P\right) \Rightarrow \left(\mathrm{Markov}\left(n + 1, P\right) \Rightarrow P = \mathrm{completion}\left(u, n\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/InhomogeneousMarkovCompletion.unique_markov_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The overlapping-table expression is itself a legal probability law, has every prescribed site mean, and is first-order Markov. Every other legal first-order Markov law with these same means equals it as a function on all Boolean words. In particular the conclusion concerns a whole finite chain at arbitrary length, rather than only its adjacent pairs.

Writing the overlapping-table quotient as an initial site mass times conditional transitions proves nonnegativity. Summing over the last bit removes one stochastic row. Repeating this operation gives every prefix marginal. The identity that a transition propagates one prescribed site table to the next then recovers all site means and normalization. A forbidden adjacent pair contributes a zero transition factor.

The cylinder extension equations are equivalent to first-order factorization, by induction on the prefix length. For uniqueness, restrict any such law to prefixes. The full-law means identify both states of each prefix endpoint. Legal support makes the true-true adjacent mass zero. Positive true marginal therefore forces the true-true transition to vanish, and its row sum forces the true-false transition to equal one. The next mean identifies the false-true transition; its row sum supplies the last entry. Thus every transition and the initial table are fixed, determining the complete law.

Strict interiority excludes zero site marginals and zero seams. The statement does not extend this quotient to boundary means. It also does not assert that a general legal law is Markov: uniqueness is restricted to the stated first-order class.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/InhomogeneousMarkovCompletion.unique_markov_completion`
- Dependency: [D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant](../../../Quantum/FockSpace/ForbiddenNeighbourDeterminant.md)
