# All-total integer extrema at replica three

## Abstract

For every total integer N >= 3, the actual order-three Gaussian genuine multi-entropy is minimized precisely by the balanced positive integer triples and maximized precisely by permutations of (N-2,1,1), with all ties retained. The two extremal classes coincide at N=3 and N=4.

Scientific source: Haobo Ma then Wenlin Zhang, An exact balancing law for order-three Gaussian multi-entropy, 4 November 2026, CC BY 4.0. Camargo and Nishida supply the physical family; Marshall, Olkin and Arnold supply the classical majorization criterion. The proof reuses the actual integral/Fourier bridge and the strict scalar comparison, retaining their canonical and transplant credits. Higher replicas, physical replica-one continuation, other branches and the separate Page/large-N issue 22644 remain outside this result.

**Definition 1.1 (The balanced representative).**

$$\forall N \in \mathbb{N}, b(N)=(\lfloor\frac{N}{3}\rfloor+\mathbf{1}_{0<mod\left(N, 3\right)},\lfloor\frac{N}{3}\rfloor+\mathbf{1}_{1<mod\left(N, 3\right)},\lfloor\frac{N}{3}\rfloor)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeExtrema.balanced` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write N=3q+r with q=N/3 and r=N%3 in {0,1,2}, and put delta_0=[r>0], delta_1=[r>1]. The descending representative has exactly r entries q+1 and the remaining entries q: (q+delta_0,q+delta_1,q). All permutations represent the same balanced class. In the extrema formulas below, b and e abbreviate b(N) and e(N).

**Definition 1.2 (The extreme representative).**

$$\forall N \in \mathbb{N}, e(N)=(N-2,1,1)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeExtrema.extreme` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The extreme positive integer representative is (N-2,1,1). Its full permutation class is retained, including the duplicate entries and the fully tied N=3 case.

**Definition 1.3 (Balanced integer triples).**

$$\forall x \in \{0,1,2\}\to \mathbb{N}, B(x) \iff \forall i \in \{0,1,2\}, \forall j \in \{0,1,2\}, x_i\le x_j+1$$

*Formalization.* `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeExtrema.IsBalanced` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A triple is balanced exactly when x_i <= x_j+1 for every ordered pair i,j, equivalently every pair of integer sizes differs by at most one. This definition does not impose an ordering on party labels.

**Theorem 1.4 (Scalar extrema and both iff equality classes).**

$$V(k,b)\le V(k,x)\le V(k,e);V(k,x)=V(k,b) \iff B(x);V(k,x)=V(k,e) \iff \exists \sigma,x=e\circ \sigma$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeExtrema.integer_extrema` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k>0, integer N>=3 and positive integer triple x of total N, V(k,balanced N) <= V(k,x) <= V(k,N-2,1,1). Equality at the minimum holds if and only if x is balanced; equality at the maximum holds if and only if x is a permutation of (N-2,1,1). The values are the exact logarithmic expression of ReplicaThreeScalar, evaluated at the displayed representatives, for all three residues of N. Sorting supplies the two prefix bounds; the strict Schur theorem supplies both permutation equality directions. This is universal in N, not a finite enumeration.

**Theorem 1.5 (Actual integral-defined physical extrema).**

$$V(k,b)\le GM_3(x,a)\le V(k,e);GM_3(x,a)=V(k,b) \iff B(x);GM_3(x,a)=V(k,e) \iff \exists \sigma,x=e\circ \sigma;k=\kappa(N,a)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeExtrema.GM3_three_extrema` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer N>=3, a>1 and positive integer labelled triple x with sum N, the actual integral-defined GaussianMultiEntropyAsymptotic.GM3 3 x_0 x_1 x_2 a lies between V(kappa,balanced N) and V(kappa,N-2,1,1), where kappa=3(a^2-1)/(4(N-1)). It equals the lower endpoint if and only if every pair of sizes differs by at most one; it equals the upper endpoint if and only if x is a permutation of (N-2,1,1). Both endpoint representatives are positive triples of the required total, so these bounds are attained. Each endpoint is the exact formula log((1+kappa s)^2/(D_x D_y D_z))/12 evaluated at its representative, with all three labelled cut factors. Physical mode counts are integers; positive reals occur only in the scalar comparison used by the proof. At a=1 the separate physical behavior theorem gives zero and all triples tie.

**Theorem 1.6 (Coincident extrema at totals three and four).**

$$B(e) \iff N=3 \lor N=4;V(k,b)=V(k,e) \iff N=3 \lor N=4$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeExtrema.extremal_degeneracy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k>0 and N>=3, the extreme representative is balanced if and only if N=3 or N=4; equivalently the minimum and maximum values coincide if and only if N=3 or N=4. Thus every admissible triple at these totals belongs to the common extremal class, with no false strict separation. For every N>=5 the two extremal values are distinct and the minimum is strictly smaller.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeExtrema.GM3_three_extrema`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeExtrema.IsBalanced`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeExtrema.balanced`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeExtrema.extremal_degeneracy`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeExtrema.extreme`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeExtrema.integer_extrema`
- Dependency: [D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThree](ReplicaThree.md)
- Dependency: [D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeMajorization](ReplicaThreeMajorization.md)
