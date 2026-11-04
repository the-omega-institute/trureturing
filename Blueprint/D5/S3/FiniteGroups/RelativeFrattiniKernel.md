# Relative Frattini Kernels

## Abstract

The automorphism and outer-automorphism kernels of a normal prime-power subgroup are prime-power groups.

**Definition 1.1 (Automorphisms preserving a specified subgroup).**

$$\forall Q \in Type,\; [\operatorname{Group}\left(Q\right)], \forall P \in \operatorname{Subgroup}\left(Q\right),\; \operatorname{preservingAut}\left(P\right) = \operatorname{Stabilizer}\left(\operatorname{MulAut}\left(Q\right), P\right)$$

*Formalization.* `D5/S3/FiniteGroups/RelativeFrattiniKernel.preservingAut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let Q be a group and P a specified subgroup. The group A consists of all automorphisms a of Q for which x belongs to P exactly when a(x) belongs to P. No characteristic-subgroup assumption is imposed on P.

**Definition 1.2 (The common subgroup inside the ambient group).**

$$\forall Q \in Type,\; [\operatorname{Group}\left(Q\right)], \forall P \in \operatorname{Subgroup}\left(Q\right),\; \operatorname{relativeFrattini}\left(P\right) = \operatorname{map}\left(\operatorname{frattini}\left(P\right), \operatorname{subtype}\left(P\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/RelativeFrattiniKernel.relativeFrattini` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write F for the image of Frattini(P) under the inclusion of P in Q. If P is normal in Q, then F is normal in Q, since Frattini(P) is characteristic in P. Every element of A preserves F.

**Definition 1.3 (Restriction to P).**

$$\forall Q \in Type,\; [\operatorname{Group}\left(Q\right)], \forall P \in \operatorname{Subgroup}\left(Q\right),\; \forall a \in \operatorname{preservingAut}\left(P\right),\; \forall x \in P,\; \operatorname{apply}\left(\operatorname{restriction}\left(P, a\right), x\right) = \operatorname{apply}\left(a, x\right)$$

*Formalization.* `D5/S3/FiniteGroups/RelativeFrattiniKernel.restriction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restriction is a homomorphism from A to Aut(P). Its inverse on each individual automorphism is the restriction of that automorphism's inverse.

**Definition 1.4 (The induced action on the actual quotient).**

$$\forall Q \in Type,\; [\operatorname{Group}\left(Q\right)], \forall P \in \operatorname{Subgroup}\left(Q\right),\; [\operatorname{Normal}\left(P\right)], \forall a \in \operatorname{preservingAut}\left(P\right),\; \forall x \in Q,\; \operatorname{apply}\left(\operatorname{apply}\left(\operatorname{quotientAction}\left(P\right), a\right), \operatorname{coset}\left(x, \operatorname{relativeFrattini}\left(P\right)\right)\right) = \operatorname{coset}\left(\operatorname{apply}\left(a, x\right), \operatorname{relativeFrattini}\left(P\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/RelativeFrattiniKernel.quotientAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The homomorphism rho from A to Aut(Q/F) sends the coset of x to the coset of a(x). Its kernel B is exactly the group of all P-preserving automorphisms inducing the identity on Q/F.

**Theorem 1.5 (The full automorphism kernel is a prime-power group).**

$$\forall Q \in Type,\; \forall group \in \operatorname{Group}\left(Q\right),\; \forall finite \in \operatorname{Finite}\left(Q\right),\; \forall P \in \operatorname{Subgroup}\left(Q\right),\; \forall normal \in \operatorname{Normal}\left(P\right),\; \forall p \in Nat,\; \forall pgroup \in \operatorname{IsPGroup}\left(p, P\right),\; \operatorname{IsPGroup}\left(p, \operatorname{ker}\left(\operatorname{quotientAction}\left(P\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/RelativeFrattiniKernel.isPGroup_automorphism_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Qiuzhen-CFSG contributors (2026). *CFSG Frattini automorphism kernel*. URL: <https://github.com/Qiuzhen-CFSG/CFSG/blob/0c6635528a02dd46f2e93e2ade0c4ac647ad1eb7/Theory/GroupTheory/PGroup/FrattiniAutomorphismKernel.lean>.

*Commentary.*

Assume Q is finite and P is a normal p-subgroup. The result is proved for every natural p satisfying IsPGroup p P; in particular it applies to every prime p. It includes P trivial, P equal to Q, trivial Frattini subgroup, noncharacteristic P, nonabelian P, nonsplit extensions and nontrivial conjugation actions.

Restrict B to P. Its image lies in the ordinary Frattini automorphism kernel of P: triviality modulo the image F inside Q pulls back to triviality modulo Frattini(P). The ordinary finite Frattini kernel theorem therefore makes this image a p-group.

Let K be the restriction kernel. Every a in K fixes P pointwise and satisfies x inverse times a(x) in F, hence in P. Define its displacement as the function d(a) from Q to P. Pointwise fixation makes displacement multiplicative under composition, even when P is nonabelian.

$$
\forall a \in K,\; \forall b \in K,\; \forall x \in Q,\; \operatorname{d}\left(\operatorname{mul}\left(a, b\right), x\right) = \operatorname{mul}\left(\operatorname{d}\left(a, x\right), \operatorname{d}\left(b, x\right)\right)
$$

The displacement is injective because its values recover a(x) for every x. A single p-power annihilates every element of finite P, so it also annihilates every function Q to P. Thus K is a p-group. The kernel-image extension argument proves that B is a p-group. The displacement method follows Theory/GroupTheory/CentralCharacteristicAutomorphisms.lean of Qiuzhen-CFSG/CFSG at revision 0c6635528a02dd46f2e93e2ade0c4ac647ad1eb7, under Apache-2.0, with the ambient automorphism group restricted to A. The ordinary Frattini theorem is reused directly.

**Definition 1.6 (The actual relative outer automorphism group).**

$$\forall Q \in Type,\; [\operatorname{Group}\left(Q\right)], \forall P \in \operatorname{Subgroup}\left(Q\right),\; [\operatorname{Normal}\left(P\right)], \operatorname{RelativeOuter}\left(P\right) = \operatorname{Quotient}\left(\operatorname{preservingAut}\left(P\right), \operatorname{relativeInner}\left(P\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/RelativeFrattiniKernel.RelativeOuter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any group G, innerAut G is the image of conjugation G to Aut(G), and OuterAut G is Aut(G) modulo that normal subgroup. The subgroup relativeInner P is the inverse image of innerAut Q under the inclusion A into Aut(Q). Since P is normal, all inner automorphisms of Q lie in A. RelativeOuter P is therefore the group of P-preserving outer automorphisms, with its actual inner equivalence relation.

**Definition 1.7 (The homomorphism on outer automorphisms).**

$$\forall Q \in Type,\; [\operatorname{Group}\left(Q\right)], \forall P \in \operatorname{Subgroup}\left(Q\right),\; [\operatorname{Normal}\left(P\right)], \forall a \in \operatorname{preservingAut}\left(P\right),\; \operatorname{apply}\left(\operatorname{outerAction}\left(P\right), \operatorname{coset}\left(a, \operatorname{relativeInner}\left(P\right)\right)\right) = \operatorname{coset}\left(\operatorname{apply}\left(\operatorname{quotientAction}\left(P\right), a\right), \operatorname{innerAut}\left(\operatorname{Quotient}\left(Q, \operatorname{relativeFrattini}\left(P\right)\right)\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/RelativeFrattiniKernel.outerAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An inner automorphism represented by q in Q induces conjugation by qF on Q/F. Consequently rho descends to a homomorphism from RelativeOuter P to OuterAut(Q/F). Both sides use the same Q, P and F as the automorphism theorem.

**Theorem 1.8 (Every restricted outer-action kernel is a prime-power group).**

$$\forall Q \in Type,\; \forall group \in \operatorname{Group}\left(Q\right),\; \forall finite \in \operatorname{Finite}\left(Q\right),\; \forall P \in \operatorname{Subgroup}\left(Q\right),\; \forall normal \in \operatorname{Normal}\left(P\right),\; \forall p \in Nat,\; \forall pgroup \in \operatorname{IsPGroup}\left(p, P\right),\; \forall H \in \operatorname{Subgroup}\left(\operatorname{RelativeOuter}\left(P\right)\right),\; \operatorname{IsPGroup}\left(p, \operatorname{ker}\left(\operatorname{comp}\left(\operatorname{outerAction}\left(P\right), \operatorname{subtype}\left(H\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/RelativeFrattiniKernel.isPGroup_outer_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be any subgroup of the relative outer group. Its restricted map to OuterAut(Q/F) has a p-group kernel. To prove this, represent an element of the full outer kernel by a in A. The induced automorphism rho(a) is conjugation by some y in Q/F. Lift y to q in Q and multiply a by the inverse of conjugation by q.

$$
b = \operatorname{mul}\left(a, \operatorname{inv}\left(\operatorname{innerLift}\left(P, q\right)\right)\right)
$$

The resulting automorphism b belongs to B and has the same relative outer class as a. Thus the full outer kernel lies in the image of B under the relative quotient map, and is a p-group. Passing to H takes a subgroup of that kernel. No lift of a group extension or compatible choice of conjugators is assumed: only the individual quotient representative is lifted.

## References

- Truth anchor: `D5/S3/FiniteGroups/RelativeFrattiniKernel.RelativeOuter`
- Truth anchor: `D5/S3/FiniteGroups/RelativeFrattiniKernel.isPGroup_automorphism_kernel`
- Truth anchor: `D5/S3/FiniteGroups/RelativeFrattiniKernel.isPGroup_outer_kernel`
- Truth anchor: `D5/S3/FiniteGroups/RelativeFrattiniKernel.outerAction`
- Truth anchor: `D5/S3/FiniteGroups/RelativeFrattiniKernel.preservingAut`
- Truth anchor: `D5/S3/FiniteGroups/RelativeFrattiniKernel.quotientAction`
- Truth anchor: `D5/S3/FiniteGroups/RelativeFrattiniKernel.relativeFrattini`
- Truth anchor: `D5/S3/FiniteGroups/RelativeFrattiniKernel.restriction`
- Dependency: [D5/S3/FiniteGroups/FrattiniAutomorphismKernel](FrattiniAutomorphismKernel.md)
