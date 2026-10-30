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

For positive activities w(i) on a path of length N=n+2, let P(b) be the product of w(i) over occupied positions, divided by the sum of those products over legal words. Extend P by zero to forbidden words. Define u(i) by taking the expectation of the indicator of occupation at i under this same P. Read false and true as the indicators zero and one throughout. The all-false word and every singleton word have positive mass. They give 0<u(i)<1 and 1-u(i)-u(i+1)>0 at every adjacent pair.

The connection with the Markov completion can be made directly on these actual weights. Put A(i,s,t)=0 when s=t=true, A(i,s,false)=1, and A(i,false,true)=w(i+1). Let B(i,s) be the sum of the remaining edge products after the bit s at i, with B(N-1,s)=1. Summing the next bit gives B(i,s)=sum_t A(i,s,t)B(i+1,t). All these suffix sums are positive, since a continuation using only false bits contributes one. Consequently K(i,s,t)=A(i,s,t)B(i+1,t)/B(i,s) has nonnegative stochastic rows. Use initial mass w(0)^s B(0,s)/Z, where Z is the actual legal-word normalizer. The suffix factors telescope along each complete word. Thus this chain has exactly mass P, including zero on forbidden words. Its cylinder identities include every history. Applying unique_markov_completion with the actual means identifies P with completion(u,n).

Under this common law set R(i)=b(i)-u(i), alpha(i)=-u(i+1)/(1-u(i)), E(0)=R(0), and E(i+1)=R(i+1)-alpha(i)R(i). The canonical transition row has mean zero when applied to E(i+1). The identities completion_chain and prefix_expect therefore give expectation zero for E(i+1) times every real function of b(0),...,b(i). In particular every distinct pair from the whole family E has product expectation zero. The finite measure assigning each word its mass P gives conditional expectation alpha(i)R(i) for R(i+1), by the characterization ae_eq_condExp_of_forall_setIntegral_eq, both when conditioning on the whole prefix and when conditioning only on b(i). These equalities hold almost everywhere under P.

The same prefix identities and endpoint_canonical reduce the square moments to the one-site and adjacent two-site tables. They give expectation E(0)^2=u(0)(1-u(0)) and expectation E(i+1)^2=u(i+1)(1-u(i)-u(i+1))/(1-u(i)). All means, transitions, innovations, moments and conditional expectations here belong to the same activity law. Null histories retain zero mass; the conditional identities assign no pointwise conditional probabilities there. The case n=0 has two sites and an empty internal denominator product equal to one. Paths with fewer than two sites and boundary means or seams are outside this application. These are finite classical probability statements; no physical realization is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/InhomogeneousMarkovCompletion.unique_markov_completion`
- Dependency: [D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant](../../../Quantum/FockSpace/ForbiddenNeighbourDeterminant.md)
