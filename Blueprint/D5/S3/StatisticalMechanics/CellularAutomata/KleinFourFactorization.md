# Membership in the lazy and invertible generated submonoid

## Abstract

Let H = Multiplicative(ZMod(2) x ZMod(2)), with alphabet Bool. Configurations are all functions H -> Bool, and the right shift is rho_g(x)(h) = x(h g). The predicates IsCA, IsLazy and IsInvertibleCA are the existing local-rule predicates: a lazy rule has exactly one active exceptional pattern on any finite neighborhood containing 1. Let W_n be the set of configurations with exactly n true cells, C the two constants, O(x) the shift orbit of x, and c_b the constant with value b. Write w_false = 1 and w_true = 3. The public theorem below transports the structural proof by E. Alcala-Arroyo, A. Castillo-Ramirez, H. Ma and W. Zhang (public supplement v1.1.0, DOI 10.5281/zenodo.23280244) to this configuration space.

**Theorem 1.1 (The structural criterion on actual configurations).**

$$\forall T \in End\left(Bool^{H}\right), IsCA\left(T\right) \implies (T \in closure\left(U \cup L\right) \Leftrightarrow ((\exists b \in Bool, T[W_{1}] = W_{w_{b}} \land T[W_{3}] = W_{w_{b}}) \Rightarrow \exists x \in Bool^{H}, b \in Bool, |O\left(x\right)| = 2 \land T[C \cup O\left(x\right)] = \{c_{b}\}))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/KleinFourFactorization.membership_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Edgar Alcalá-Arroyo; Alonso Castillo-Ramirez; Haobo Ma; Wenlin Zhang (2026). *Supplementary material for Generation by lazy and invertible cellular automata over the Klein four-group*. DOI: [10.5281/zenodo.23280244](https://doi.org/10.5281/zenodo.23280244). URL: <https://github.com/the-omega-institute/klein-four-lazy-ca-supplement/tree/fae47ad9dbbd4cbc1462a058dffe6ad4c2e416f1>.

*Commentary.*

U comprises all maps satisfying IsInvertibleCA and L all maps satisfying IsLazy. The generated submonoid includes the identity, represented by the empty word. A common image W_(w_b) in the antecedent is a free orbit; images that are constant or two-point orbits do not activate this condition. The consequent states equality of the image of C union O(x) with the singleton {c_b}, where O(x) has two points.

The seven-orbit representation is bijective with all configurations. Sending false and true to 0 and 1 in each group coordinate identifies xor with multiplication in H and carries the model action to the right shift. Conjugation identifies every model equivariant map with a cellular automaton; conversely every cellular automaton commutes with shifts and gives a model equivariant map. On this finite group every equivariant map has a full-neighborhood local rule. The lazy generators correspond in both directions by transporting the neighborhood and exceptional pattern, extending that pattern arbitrarily outside its neighborhood. Bijectivity gives an equivariant inverse and hence agrees with IsInvertibleCA. These identities transport both inclusions of the generated closure.

For the reverse implication, a nonmerging map factors into elementary collapses, independent lower-stratum actions and a unit extending the partial permutation on the free strata. A merging map with the stated witness factors through B_s, followed and preceded by nonmerging maps. With k_s the nonidentity group element selected by the index s, the transported coordinate rule is B_s(x)(g) = x(g) and not x(g k_s). Every factor belongs to the full lawful generating family. Weight-one and weight-three configurations are exactly the two model free strata, and the three model pair strata exhaust all two-point shift orbits. No fixed cardinality of a generated monoid, shortest-word result or lazy-only sufficient condition is asserted.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/KleinFourFactorization.membership_iff`
- Dependency: [D5/S3/StatisticalMechanics/CellularAutomata/KleinFourInvariant](KleinFourInvariant.md)
- Dependency: [D5/S3/StatisticalMechanics/CellularAutomata/LazyInvertibleGeneration](LazyInvertibleGeneration.md)
