# The Ordinary Frattini Automorphism Kernel

## Abstract

Automorphisms of a finite prime-power group acting trivially on its Frattini quotient form a prime-power group.

**Definition 1.1 (The action on a characteristic quotient).**

$$\forall G \in Type,\; \forall group \in \operatorname{Group}\left(G\right),\; \forall C \in \operatorname{Subgroup}\left(G\right),\; \forall characteristic \in \operatorname{Characteristic}\left(C\right),\; \forall a \in \operatorname{MulAut}\left(G\right),\; \forall g \in G,\; \operatorname{quotientAut}\left(C, a, \operatorname{coset}\left(g, C\right)\right) = \operatorname{coset}\left(\operatorname{apply}\left(a, g\right), C\right)$$

*Formalization.* `D5/S3/FiniteGroups/FrattiniAutomorphismKernel.quotientAut` (`✓ std3`).

*Citation.* Qiuzhen-CFSG contributors (2026). *CFSG Frattini automorphism kernel*. URL: <https://github.com/Qiuzhen-CFSG/CFSG/blob/0c6635528a02dd46f2e93e2ade0c4ac647ad1eb7/Theory/GroupTheory/PGroup/FrattiniAutomorphismKernel.lean>.

*Commentary.*

For a characteristic subgroup C of a group G, quotientAut C sends an automorphism a to the induced automorphism of G/C. On a coset represented by g its value is the coset represented by a(g). The construction is a homomorphism, with multiplication given by composition.

**Theorem 1.2 (The kernel is a prime-power group).**

$$\forall G \in Type,\; \forall group \in \operatorname{Group}\left(G\right),\; \forall finite \in \operatorname{Finite}\left(G\right),\; \forall p \in \mathbb{N},\; \operatorname{IsPGroup}\left(p, G\right) \Rightarrow \operatorname{IsPGroup}\left(p, \operatorname{ker}\left(\operatorname{quotientAut}\left(\operatorname{frattini}\left(G\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FrattiniAutomorphismKernel.isPGroup_quotientAut_frattini_kernel` (`✓ std3`). ∎

*Citation.* Qiuzhen-CFSG contributors (2026). *CFSG Frattini automorphism kernel*. URL: <https://github.com/Qiuzhen-CFSG/CFSG/blob/0c6635528a02dd46f2e93e2ade0c4ac647ad1eb7/Theory/GroupTheory/PGroup/FrattiniAutomorphismKernel.lean>.

*Commentary.*

Let G be any finite group and let p be a natural number. If every element of G has order dividing a power of p, the same holds for the kernel of Aut(G) to Aut(G/Frattini(G)). In particular this holds for every finite p-group with p prime, including the trivial group. No nontriviality, splitting, coprimality or extra automorphism hypothesis is imposed.

Write C for Frattini(G) and K for this kernel. Consider all functions f from G to C, interpreted as the ordered family g f(g). For a in K the action sends f(g) to g inverse times a(g f(g)). This belongs to C because a acts trivially modulo C and preserves C.

An automorphism stabilizing such a family fixes every g f(g). Its equalizer subgroup E with the identity satisfies E join C equal to G: multiply the fixed element g f(g) by f(g) inverse to obtain g. The nongenerating property of the Frattini subgroup forces E to be G. Thus every stabilizer is trivial.

Orbit decomposition identifies the function space with its orbit quotient times K. Hence the order of K divides the number of functions, which is the order of C raised to the order of G. Since C is a subgroup of the given p-group, this cardinality divides a power of p.

This is the ordinary automorphism-kernel statement. It does not assert the commutator-and-powers formula for the Frattini subgroup, nor the relative or outer-automorphism kernel theorem for a normal subgroup of a larger finite group.

## References

- Truth anchor: `D5/S3/FiniteGroups/FrattiniAutomorphismKernel.isPGroup_quotientAut_frattini_kernel`
- Truth anchor: `D5/S3/FiniteGroups/FrattiniAutomorphismKernel.quotientAut`
