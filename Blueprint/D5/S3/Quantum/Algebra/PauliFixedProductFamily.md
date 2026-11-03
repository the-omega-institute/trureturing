# Fixed positive tensor product and the complete Pauli residual

## Abstract

Fixed spin products carry an actual real Pauli perturbation with a complete unaveraged residual.

The local space is real Euclidean four-space, ordered as scalar, x, y, z. Its spin multiplication sends (a,v),(b,w) to (ab+v dot w, aw+bv), and its fixed cross channel sends them to (0,v cross w). The action D(t) replaces the first cross label v by v+taz, for every real t. The local Euclidean inner product and multiplication are fixed. The joint carrier is the actual real Hilbert tensor product with its positive product inner product.

On pure tensors, the joint multiplication is spin tensor spin minus cross tensor cross. The cross channels in that multiplication remain fixed. The actual joint action on a simple label is D tensor left multiplication plus left multiplication tensor D. Bilinear maps and the tensor universal property extend the definitions to every joint input. The residual E is Gamma applied to the product minus the two terms obtained by applying Gamma to one product input. No arbitrary residual table or global derivation law is assumed.

**Theorem 1.1 (The actual residual scales on all joint inputs).**

$$\forall t,H,X,Y, \operatorname{E}(t,H,X,Y)=t \operatorname{E}(1,H,X,Y)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PauliFixedProductFamily.residual_scaling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The local label action is affine in t, hence so are the actual joint action and its trilinear residual. At t=0 the residual vanishes on the entire joint carrier. This follows from its exact values on the complete product basis and trilinearity, extended through the basis span in each of the three slots. Therefore E(t,H,X,Y)=t E(1,H,X,Y) for arbitrary H,X,Y, including arbitrary sums of pure tensors.

**Theorem 1.2 (All ordered labels and every output coordinate).**

$$\forall t \in \mathbb{R}, \operatorname{reportSquared}(t)=288t^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PauliFixedProductFamily.full_report` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The report sums squared output norms over all three copies of the complete sixteen-element product basis. There is no average over its 4096 ordered triples; each output norm includes every output coordinate in the fixed positive product metric. At parameter one, six first-input blocks contribute forty-eight each and all ten other first-input blocks vanish. The block with first label 1 tensor z has zero rows when both second-input factors are 1 or z, and squared row sum four otherwise. All block values are evaluated from the actual bilinear product and joint action, and all-input residual scaling gives 288t squared.

**Theorem 1.3 (The fixed realization satisfies all four original identities).**

$$\forall t, \operatorname{fixedRealization}(t)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PauliFixedProductFamily.family_contract` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The local dimension is four and the joint dimension is sixteen. The local basis is a complete orthonormal basis with elements 1,x,y,z, and its tensor product is the complete joint orthonormal basis used by the report. The spin multiplication is commutative, has unit 1, and is Frobenius. Every D(t,a) is an exact local derivation on all inputs, and D(t,x,y)=z shows activity for every t. The fixed M is commutative, has unit 1 tensor 1, and is Frobenius for the same positive product inner product; the squared self-inner-product is nonnegative and vanishes exactly at zero. For all local a,b,c,d, M(a tensor 1,c tensor d)=S(a,c) tensor d and M(1 tensor b,c tensor d)=c tensor S(b,d). For all the same inputs, Gamma(t,a tensor b,c tensor 1)=D(t,a,c) tensor b and Gamma(t,a tensor b,1 tensor d)=a tensor D(t,b,d). The theorem also retains the exact complete residual square 288t squared. These are identities of the actual maps, without alternation, Jacobi or vanishing of the unit generator as assumptions.

The direct spin-factor construction establishes the required algebraic realization without a physical supply conclusion. It proves no general stability theorem for arbitrary joint products, no acquisition procedure and no noisy reconstruction of physical objects.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/PauliFixedProductFamily.family_contract`
- Truth anchor: `D5/S3/Quantum/Algebra/PauliFixedProductFamily.full_report`
- Truth anchor: `D5/S3/Quantum/Algebra/PauliFixedProductFamily.residual_scaling`
