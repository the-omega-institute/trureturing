# Actual F2 Coverage of the Independent Insertion Layer

## Abstract

Every actual configuration in the independently defined two-label insertion layer belongs to the concrete F2 supplier union, and conversely.

The base circle is the identity tuple with labels zero and m erased. Layer({0,m},P) is specified before any walk: erasing those two labels from the actual configuration must give P or its reverse. F2Domain is the previously defined two-star CoreDomain and the complete stars at every tuple (1,...,j+1,m,j+2,...,m-1,0), j in Fin(m-2).

**Theorem 1.1 (Concrete F2 Suppliers Exhaust the Independent Layer).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\forall v \in \mathrm{Configuration}\left(m\right),\; \mathrm{F2Domain}\left(m, v\right) \Leftrightarrow \mathrm{Layer}\left(\mathrm{FinsetPair}\left(0, \mathrm{FinLast}\left(m\right)\right), \mathrm{erase}\left(\mathrm{FinsetPair}\left(0, \mathrm{FinLast}\left(m\right)\right), \mathrm{configurationCycle}\left(\mathrm{identity}\left(m\right)\right)\right), v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2Coverage.native_f2_layer_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least four and every actual permutation v, F2Domain(m,v) holds exactly when v belongs to the independently specified two-label insertion layer over the erased identity circle. This closes the coverage gap between the finite graft construction and the insertion layer; no support definition or configuration search is assumed.

Write B=(1,...,m-1). The generic childDomain_exists theorem orients the actual residual after deleting zero so that deleting m gives B. The existing cyclic gap fiber theorem then gives a unique gap r in Fin(m-1), with residual circle (m,B.rotate(r)).

Gap zero is the lower shadow supplier: rotating its actual residual by m-2 gives (m,B). Every positive gap r is the concrete contact j=r-1: rotating that residual by j+1 gives (m,B.rotate(j+1)). These exhaust all oriented children and hence cover every actual configuration, including the negatively oriented case supplied by the generic insertion-layer theorem.

Conversely, deleting m from each of these residuals gives B. The upper supplier is the image of the lower residual under swapping zero and m; this swap fixes every label of B, so deleting zero from its residual also gives B. Both core stars and every contact star therefore lie wholly inside the independent two-label layer.

Combining this equality of independently specified domains with the existing finite F2 Hamilton-cycle construction identifies its spanning domain. The later marked-path recombination and recursive Hamiltonicity of the entire native graph require their separate proofs.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2Coverage.native_f2_layer_iff`
- Dependency: [D5/S3/Combinatorics/CircularWords/CyclicInsertionGap](../../CircularWords/CyclicInsertionGap.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/InsertionLayerPartition](InsertionLayerPartition.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeContactIteration](NativeContactIteration.md)
