# Supported fixed outputs and calibrating seeds

## Abstract

Stabilizers of positive seeds for finite covariant probability kernels.

**Theorem 1.1 (A specified subgroup can fix a positive seed).**

$$\operatorname{CovariantKernel}\left(P\right) \Rightarrow (\operatorname{HasSeedFixedBy}\left(P, H\right) \iff \operatorname{SupportedFixedOutputs}\left(P, H\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/FiniteKernelStabilizers.stabilizer_possible_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A group G acts on a finite input set X and a finite output set Y. P is a nonnegative real kernel, each row sums to one, and P evaluated at g acting on x and y equals P at x and y. H is a subgroup of G.

HasSeedFixedBy means there is a finite G-set of seeds with positive invariant real weights summing to one and a covariant deterministic readout on inputs and seeds. The mass of seeds sent to y at x is P(x,y). Some seed is fixed by every element of H. SupportedFixedOutputs means that for every x, there is a y of positive row mass fixed by every element of H fixing x.

A fixed seed yields a supported output by positivity and covariance. For the converse, choose a supported fixed output at one representative of each H-orbit of inputs and transport it over that orbit. This produces an H-equivariant table. On all tables choosing positive entries, assign each table the product of its row probabilities. Relabeling both the inputs and the outputs preserves the product. Finite product distributivity gives each required marginal. The chosen table has positive mass and is fixed by H.

**Theorem 1.2 (A prescribed subgroup can be the full stabilizer).**

$$\operatorname{CovariantKernel}\left(P\right) \land \operatorname{FiniteIndex}\left(H\right) \Rightarrow (\operatorname{HasSeedWithStabilizer}\left(P, H\right) \iff \operatorname{SupportedFixedOutputs}\left(P, H\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/FiniteKernelStabilizers.exact_stabilizer_possible_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the same kernel assumptions and require that the left coset space of H in G is finite. HasSeedWithStabilizer strengthens the existence clause to a seed whose full stabilizer is H.

Start with a seed fixed by H. Enlarge the seed space by an independent uniform left coset. Ignore that coordinate when reading the output. The product action preserves this law and the marginal masses. At the original seed paired with the identity coset, the stabilizer is the intersection of the original stabilizer with H, hence H.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/FiniteKernelStabilizers.exact_stabilizer_possible_iff`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/FiniteKernelStabilizers.stabilizer_possible_iff`
