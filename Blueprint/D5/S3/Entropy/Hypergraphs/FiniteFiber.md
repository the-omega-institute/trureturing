# Finite coordinate fibres and their exact averages

## Abstract

Finite uniform coordinate fibres and disjoint coordinate-block averages.

These are proof-organizing auxiliaries consumed by the full circular-orientation entropy lower bound, not independent escape witnesses. A finite uniform mean is a sum divided by the cardinality of its finite domain, with that cardinality cast to the scalar field. All restrictions below retain the actual coordinate values.

**Theorem 1.1 (Disjoint coordinate blocks factor a uniform average).**

Lean statement: `D5/S3/Entropy/Hypergraphs/FiniteFiber.block_average_product`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Hypergraphs/FiniteFiber.block_average_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let ι and J be arbitrary finite types, with decidable equality on ι. Let β:ι→Type have a nonempty finite fibre β(i) for every i. Let D:J→Finset ι satisfy Disjoint(D(j),D(k)) whenever j≠k. For every real-valued family F_j:(Π i∈D(j),β(i))→ℝ, the mean over all o:Π i:ι,β(i) of Π j:J F_j(o restricted to D(j)) equals the product over j of the mean of F_j over its whole block choice space. Coordinates outside every D(j) are allowed; their multiplicity cancels in the normalized average. Empty J and empty blocks are not excluded. No independence premise beyond the actual uniform product choice space and disjoint coordinate supports is imposed.

**Theorem 1.2 (An exact two-block event average).**

Lean statement: `D5/S3/Entropy/Hypergraphs/FiniteFiber.two_block_event_average`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Hypergraphs/FiniteFiber.two_block_event_average` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let ι have decidable equality, not necessarily be finite. Every β(i) is a nonempty finite type with decidable equality. Let L,R:Finset ι be disjoint, and choose u:Π i∈L,β(i) and v:Π i∈R,β(i). For arbitrary real A,B,z, assume A is exactly the uniform mean of the indicator that all L choices differ from u, and B is exactly the uniform mean of the indicator that all R choices differ from v. Over the full choice space on L∪R, average z when all L choices avoid u and not all R choices avoid v, and average 1 otherwise. The result is exactly 1−A(1−B)+A(1−B)z. Thus the event requires at least one R hit, not all R hits. The input values A and B are constrained by the two stated actual counting equalities.

**Theorem 1.3 (Averaging bounds for complex fibre means).**

Lean statement: `D5/S3/Entropy/Hypergraphs/FiniteFiber.double_uniform_mean_norm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Hypergraphs/FiniteFiber.double_uniform_mean_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary nonempty finite types A and B, f:A→B→ℂ and W:A→B→ℝ, assume for every a:A and b:B that the norm of the uniform B-mean of f(a,·) is at most W(a,b). Then the norm of the uniform A×B-mean of f is at most the uniform A×B-mean of W. W need not be independent of or constant in its second argument. The hypothesis holds for every b; it is not merely a bound for one selected representative.

**Definition 1.4 (Dependent choices are exactly valid orientations).**

Lean statement: `D5/S3/Entropy/Hypergraphs/FiniteFiber.selectedChoiceEquiv`

*Formalization.* `D5/S3/Entropy/Hypergraphs/FiniteFiber.selectedChoiceEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an arbitrary finite index type ι with decidable equality, any type V with decidable equality, and E:ι→Finset V, this is an equivalence from Π i:ι,↥(E(i)) to ↥(Fintype.piFinset E). The forward map forgets each coordinate's membership proof and retains the same V-valued function. The inverse recovers its coordinate membership proofs. Neither nonemptiness nor constant edge cardinality is required.

**Definition 1.5 (Complete the revealed and selected coordinates).**

Lean statement: `D5/S3/Entropy/Hypergraphs/FiniteFiber.splitCompletion`

*Formalization.* `D5/S3/Entropy/Hypergraphs/FiniteFiber.splitCompletion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the same ι,V,E and any S:Finset ι, take a:Π i∉S,↥(E(i)) and b:Π i∈S,↥(E(i)). The returned complete dependent choice uses b(i) when i∈S and a(i) otherwise. Its value lies in E(i) at every coordinate.

**Definition 1.6 (The revealed-selected product equivalence).**

Lean statement: `D5/S3/Entropy/Hypergraphs/FiniteFiber.splitChoiceEquiv`

*Formalization.* `D5/S3/Entropy/Hypergraphs/FiniteFiber.splitChoiceEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the same ι,V,E,S, this equivalence maps Π i:ι,↥(E(i)) to (Π i∉S,↥(E(i))) × (Π i∈S,↥(E(i))). The complement or revealed choices are the first component; selected choices are the second. Its inverse is the completion map with this same order of arguments.

**Definition 1.7 (Vertices seen in the revealed coordinates).**

Lean statement: `D5/S3/Entropy/Hypergraphs/FiniteFiber.splitRevealedImage`

*Formalization.* `D5/S3/Entropy/Hypergraphs/FiniteFiber.splitRevealedImage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the same ι,V,E,S and revealed assignment a:Π i∉S,↥(E(i)), this finite set is Finset.univ.image (fun i => (a i).val), with the index ranging over the subtype of coordinates outside S. Repeated vertices count once.

**Theorem 1.8 (The characteristic generating function of an actual fibre).**

Lean statement: `D5/S3/Entropy/Hypergraphs/FiniteFiber.split_fiber_average`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Hypergraphs/FiniteFiber.split_fiber_average` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let ι be finite with decidable equality and let V have decidable equality. Let E:ι→Finset V and S:Finset ι. Assume E(i) and E(j) are disjoint for every two distinct selected coordinates i,j∈S. Let r:ℕ be positive and assume |E(i)|=r for every i:ι, including revealed coordinates. Fix any revealed assignment a:Π i∉S,↥(E(i)) and any complex z. Put O=splitRevealedImage E S a and k_i=|E(i)∖O|. Average exp(z times the cardinality of the image of splitCompletion E S a b) over every selected assignment b:Π i∈S,↥(E(i)). The exact result is exp(z|O|) times Π i∈S (1−k_i/r+(k_i/r)exp(z)), where every count is cast to ℂ. The normalization is the cardinality of the entire selected-choice space. No restriction to imaginary z is made; empty S is permitted. The k_i are actual set-difference cardinalities, not free Bernoulli parameters or an assumed conditional-law decomposition.

## References

- Truth anchor: `D5/S3/Entropy/Hypergraphs/FiniteFiber.block_average_product`
- Truth anchor: `D5/S3/Entropy/Hypergraphs/FiniteFiber.double_uniform_mean_norm_le`
- Truth anchor: `D5/S3/Entropy/Hypergraphs/FiniteFiber.selectedChoiceEquiv`
- Truth anchor: `D5/S3/Entropy/Hypergraphs/FiniteFiber.splitChoiceEquiv`
- Truth anchor: `D5/S3/Entropy/Hypergraphs/FiniteFiber.splitCompletion`
- Truth anchor: `D5/S3/Entropy/Hypergraphs/FiniteFiber.splitRevealedImage`
- Truth anchor: `D5/S3/Entropy/Hypergraphs/FiniteFiber.split_fiber_average`
- Truth anchor: `D5/S3/Entropy/Hypergraphs/FiniteFiber.two_block_event_average`
