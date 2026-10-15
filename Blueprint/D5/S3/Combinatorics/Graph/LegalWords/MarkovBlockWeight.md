# Legal Markov block weights and persistent mixture minors

## Abstract

The ordered transition product of a legal binary block separates into a boundary factor and a power of its occupation activity, and is strictly positive.

A block w is a Boolean function on Fin n. The two exterior bits l and r are observed separately. Adm on Fin.cons l (Fin.snoc w r) requires every adjacent pair in this whole padded path to avoid two ones. No endpoints are identified. Write k(w) for the sum of (w i).toNat, where false.toNat is zero and true.toNat is one.

The hard-core path-weight identity is classical; Lemma 6.1 of Mukhamedov and Suhov gives its endpoint-dependent cylinder form. Here their transition parameters are 1-p and p, their activity is p/(1-p)^2, and their path is the padded block. Dividing their cylinder mass by its positive initial stationary mass gives this ordered transition product. For a parameter p, transition p has entries 1-p, p, 1, 0 in row order (false,false), (false,true), (true,false), (true,true). pathMass p n l w r is the actual ordered product from l through all n bits of w to r. At n=0 it is transition p l r; at n+1 it is transition p l (w 0) times pathMass p n (w 0) (Fin.tail w) r.

**Theorem 1.1 (Boundary factor and activity at every positive length).**

$$\forall p \in \mathbb{R},\; (0 < p \land p < 1) \Rightarrow (\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\forall l \in \mathrm{Bool},\; \forall r \in \mathrm{Bool},\; \forall w \in \mathrm{Fin}\left(n\right) \to \mathrm{Bool},\; (\mathrm{Adm}\left(n + 2, \mathrm{cons}\left(l, \mathrm{snoc}\left(w, r\right)\right)\right)) \Rightarrow (\mathrm{pathMass}\left(p, n, l, w, r\right) = (p)^{\mathrm{toNat}\left(r\right)} \cdot (1 - p)^{n + 1 - \mathrm{toNat}\left(l\right) - \mathrm{toNat}\left(r\right)} \cdot (\frac{p}{(1 - p)^{2}})^{\sum_{i: \mathrm{Fin}\left(n\right)} \mathrm{toNat}\left(\mathrm{w}\left(i\right)\right)} \land 0 < \mathrm{pathMass}\left(p, n, l, w, r\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/MarkovBlockWeight.path_weight_formula` (`✓ std3`). ∎

*Citation.* Farrukh Mukhamedov and Yuri Suhov (2026). *Quasi-Product States and Factor Types for the One-Dimensional Hard-Core Model*. URL: <https://arxiv.org/abs/2606.12458v2>.

*Commentary.*

For every real p strictly between zero and one, every n at least one, both Boolean exterior bits and every legal padded block, the product equals the displayed expression and is strictly positive. Exponents are natural numbers; subtraction in the boundary exponent uses natural subtraction, and n+1 is at least l.toNat+r.toNat. With z=p/(1-p)^2, dependence on w is exactly z to the power k(w). The boundary factor depends only on p, n, l and r.

Induct on the block length with the boundary exponent temporarily interpreted as an integer. The empty path has three allowed endpoint pairs, checked directly. At a new first bit, the false-false transition supplies one factor 1-p, false-true supplies p and one occupation, and true-false supplies one. The true-true case is excluded by Adm. Integer power addition accounts for the boundary shift; positivity of 1-p permits cancellation. At positive length the integer exponent agrees with the natural exponent. Every factor on the right is positive.

The formula applies in particular to every component parameter between 1/3 and 3/8. It includes n=1 and forced boundary bits. For l=r=true and n=1, the only legal block is false and its mass is p. This gives the transition-product arithmetic for conditioning an interior interval. A full conditional law also needs cancellation of the exterior factors and normalization over legal completions. Blocks touching an open endpoint require their actual stationary endpoint factors.

**Theorem 1.2 (Positive explicit minor of normalized legal Markov mixtures).**

$$\forall n \in \mathbb{N},\; \forall p \in \mathrm{Fin}\left(n + 1\right) \to \mathbb{R},\; \forall t \in \mathrm{Fin}\left(n + 1\right) \to \mathbb{R},\; (\left(\left(\forall k \in \mathrm{Fin}\left(n + 1\right),\; 0 < \mathrm{p}\left(k\right) \land \mathrm{p}\left(k\right) < 1\right) \land \mathrm{StrictMono}\left(p\right)\right) \land \left(\forall k \in \mathrm{Fin}\left(n + 1\right),\; 0 < \mathrm{t}\left(k\right)\right)) \Rightarrow (\forall l \in \mathrm{Bool},\; \forall r \in \mathrm{Bool},\; \mathrm{Injective}\left(\mathrm{halfWord}\left(n\right)\right) \land \left(\mathrm{det}\left(\mathrm{cutMinor}\left(n, p, t, l, r\right)\right) = \prod_{k: \mathrm{Fin}\left(n + 1\right)} \frac{\mathrm{t}\left(k\right)}{\mathrm{activityPartition}\left(\mathrm{p}\left(k\right), 2 \cdot n + 1 + 2 \cdot n + 1, l, r\right)} \cdot (\prod_{i: \mathrm{Fin}\left(n + 1\right)} \prod_{j\in \mathrm{Ioi}\left(i\right)} (\frac{\mathrm{p}\left(j\right)}{(1 - \mathrm{p}\left(j\right))^{2}} - \frac{\mathrm{p}\left(i\right)}{(1 - \mathrm{p}\left(i\right))^{2}}))^{2} \land 0 < \mathrm{det}\left(\mathrm{cutMinor}\left(n, p, t, l, r\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/MarkovBlockWeight.persistent_mixture_minor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Farrukh Mukhamedov and Yuri Suhov (2026). *Quasi-Product States and Factor Types for the One-Dimensional Hard-Core Model*. URL: <https://arxiv.org/abs/2606.12458v2>.

*Commentary.*

For every natural N, choose N+1 component parameters p in (0,1) strictly increasing in their Fin order, and positive weights t. The result therefore includes N at least two, parameters between 1/3 and 3/8, and posterior weights summing to one. No weight-sum hypothesis is needed for this determinant identity. Both actual exterior bits l and r range independently over Bool.

Let m=(2N+1)+(2N+1)=4N+2. pathNormalizer(p,m,l,r) sums pathMass over all Boolean length-m words whose padded path is Adm, assigning zero to every other word. activityPartition(p,m,l,r), written Z(p,m,l,r), sums z(p) to the occupation count over that same set, with z(p)=p/(1-p)^2. conditionalMixture(p,t,m,l,r,w) is the sum over components of t(k) times their actual pathMass divided by their pathNormalizer. Thus normalization uses the actual transition products and the full legal completion set.

halfWord(N,j) is 0(10)^j followed by 2(N-j) zeros: at zero-based coordinate u it is true exactly when u is odd and u<2j. It has length 2N+1, starts and ends in zero, and contains exactly j ones. selectedWord(N,i,j) concatenates these two halves. Every selected word is legal for all four choices of exterior bits, including the seams and the middle cut, and has i+j ones. The map j to halfWord(N,j) is injective, since equal words have equal occupation counts. cutMinor(N,p,t,l,r) is the square matrix whose (i,j) entry is conditionalMixture at selectedWord(N,i,j), for i,j in Fin(N+1).

The path-weight formula factors the positive boundary factor out of pathNormalizer, leaving Z. The completion set contains selectedWord(N,0,0), so Z is positive. Therefore the selected entry is the sum of c(k) z(p(k))^(i+j), where c(k)=t(k)/Z(p(k),m,l,r)>0. The explicit counting bijection sends each occupied coordinate 2k+1 to k; adjacency and endpoint checks establish the legal-word bridge to these entries. With V(k,i)=z(p(k))^i, the matrix equals V-transpose times diag(c) times V. The Vandermonde determinant identity gives the displayed formula. The activity is strictly increasing on (0,1), so its nodes are distinct and the squared Vandermonde determinant is positive.

This is the explicit-minor arithmetic for an interior block with both exterior observations present. It does not identify posterior weights from an entire complement, prove the stationary common-matrix representation, or establish the positive minimum of the rank-constrained discrepancy. Those require their separate probabilistic and compactness hypotheses. No fictitious exterior bits are assigned to open-endpoint blocks.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/MarkovBlockWeight.path_weight_formula`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/MarkovBlockWeight.persistent_mixture_minor`
- Dependency: [D5/S1/Words/AdmissibleWords/AdmissibleCount](../../../../S1/Words/AdmissibleWords/AdmissibleCount.md)
- Dependency: [D5/S3/Quantum/Entanglement/PhaseHistoryBound](../../../Quantum/Entanglement/PhaseHistoryBound.md)
- Dependency: [D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant](../../../Quantum/FockSpace/ForbiddenNeighbourDeterminant.md)
