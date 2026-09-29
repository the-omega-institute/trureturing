# Factorial Representatives of Profinite Integers

## Abstract

Factorial-stage natural representatives converge to each compatible-residue profinite integer.

**Definition 1.1 (The factorial-stage representative).**

$$\forall x \in ProfiniteIntegers, n \in \mathbb{N},\; factorialRepresentative\left(x, n\right) = val\left(x_{{n! - 1}}\right)$$

*Formalization.* `D5/S1/Dynamics/ProfiniteFactorialApproximation.factorialRepresentative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At stage n, the coordinate with modulus n factorial has a unique representative between zero and n factorial minus one. The definition selects that natural number.

**Theorem 1.2 (The embedded representatives converge).**

$$\forall x \in ProfiniteIntegers,\; Tendsto\left((n \mapsto natEmbedding\left(factorialRepresentative\left(x, n\right)\right)), atTop, nhds\left(x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/ProfiniteFactorialApproximation.natEmbedding_factorialRepresentative_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fixed coordinate m, every factorial stage n with n at least m + 1 has m + 1 dividing n factorial. Compatibility therefore reduces the chosen stage representative exactly to the m-th coordinate of x.

Each coordinate is consequently equal to its target eventually. Coordinatewise convergence in the product topology, followed by the induced subtype topology, gives convergence to x.

The exact representative sequence and convergence statement are repo-derived. They strengthen density by providing a canonical approximating sequence for every compatible residue family.

## References

- Truth anchor: `D5/S1/Dynamics/ProfiniteFactorialApproximation.factorialRepresentative`
- Truth anchor: `D5/S1/Dynamics/ProfiniteFactorialApproximation.natEmbedding_factorialRepresentative_tendsto`
- Dependency: [D5/S1/Dynamics/ProfiniteIntegers](ProfiniteIntegers.md)
