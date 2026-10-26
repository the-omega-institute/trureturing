# Rootless Lattice Low Grades and Canonical Sugawara Spectrum

## Abstract

Constructive low-energy bijections on the actual rootless lattice carrier.

D is ordinary even integral LatticeData of any natural rank, including zero. Only real positive definiteness of the Gram matrix and absence of norm-two integral charges are required for the spectral conclusion. No unimodularity, dimension premise, fixed shell count or finite classification is used.

The new mathematical content is the exhaustive constructive oscillator and all-charge energy-two classification and its injective/surjective occupation maps. Auxiliary rewrites, stars-and-bars cardinality and basis/eigenspace transport are consumed on the live derivation of the general spectral theorem; they are not independent novelty claims. The module has admission basis escape-witness and utility none: its content is a symbolic construction for arbitrary rank, rather than bounded enumeration or a certified numerical instance.

The proof reuses chargeSublevel_finite, gradeBasis, grade_finiteDimensional, complex_inverse_exists and actualL0_eigenspace_eq_grade. Both inverse equations identify the literal canonical Sugawara L0 eigenspaces with the existing grades on the same carrier. Finite dimensionality includes every signed integer grade. Rank 24 specializes the neutral term to 324; the charged contribution remains Nat.card of the actual norm-four shell. No Leech count or Monster/moonshine identification follows from this slice.

**Definition 1.1 (Exact oscillator energy fibre).**

Lean statement: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.OscillatorFiber`

*Formalization.* `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.OscillatorFiber` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Exponent vectors with oscillatorEnergy exactly n.

**Definition 1.2 (Actual integral norm-four shell).**

Lean statement: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.NormFour`

*Formalization.* `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.NormFour` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The subtype of actual charges a with bilinear(D,a,a)=4; no finite classification or cardinality is assumed.

**Theorem 1.3 (Exhaustive energy-one oscillator classification).**

Lean statement: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.oscillator_one_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.oscillator_one_iff` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Removing one occupied occurrence proves that energy one is exactly one mode-one colour, including rank zero.

**Definition 1.4 (Energy-one oscillator bijection).**

Lean statement: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.oscillatorOneEquiv`

*Formalization.* `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.oscillatorOneEquiv` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The proved classification yields a bijection of the actual energy-one exponent fibre with Fin(rank).

**Theorem 1.5 (Exhaustive energy-two oscillator classification).**

Lean statement: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.oscillator_two_classification`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.oscillator_two_classification` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Removing an occupied occurrence leaves weight zero or one. Every energy-two exponent is a mode-two singleton or the sum of two mode-one singletons.

**Definition 1.6 (Unordered pair occupation vector).**

Lean statement: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.pairOccupation`

*Formalization.* `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.pairOccupation` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

A literal two-multiset of colours is mapped to its natural-valued finite-support occupation vector. Repeated colours are included.

**Definition 1.7 (Constructed energy-two oscillator labels).**

Lean statement: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.oscillatorTwoDecode`

*Formalization.* `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.oscillatorTwoDecode` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The two summands construct actual exponent vectors: a mode-two singleton or an unordered pair of mode-one colours.

**Definition 1.8 (Constructive oscillator energy-two equivalence).**

Lean statement: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.oscillatorTwoEquiv`

*Formalization.* `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.oscillatorTwoEquiv` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The decoder is injective and surjective, giving OscillatorFiber(D,2) equivalent to Fin(rank) + Sym(Fin(rank),2).

**Theorem 1.9 (General neutral oscillator cardinality).**

Lean statement: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.neutral_energy_two_card`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.neutral_energy_two_card` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The constructive equivalence and Mathlib stars-and-bars give rank + choose(rank+1,2).

**Theorem 1.10 (Rootless nonzero charge energy gap).**

Lean statement: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.chargeEnergy_gap`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.chargeEnergy_gap` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Positivity and evenness give nonnegative integral half-norm; zero characterizes the zero charge and rootlessness excludes energy one. Every nonzero charge costs at least two.

**Theorem 1.11 (Derived finiteness of the actual norm-four shell).**

Lean statement: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.normFour_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.normFour_finite` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The actual shell embeds in the existing charge-energy sublevel at two, whose finiteness follows from positive definiteness.

**Theorem 1.12 (All-charge energy-one exclusion).**

Lean statement: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.energy_one_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.energy_one_iff` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Total energy one forces zero charge and oscillator energy one.

**Theorem 1.13 (All-charge energy-two classification).**

Lean statement: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.energy_two_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.energy_two_iff` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Total energy two is exactly a neutral weight-two oscillator or a norm-four charge with zero oscillator exponent.

**Definition 1.14 (Vacuum energy label).**

Lean statement: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.energyZeroEquiv`

*Formalization.* `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.energyZeroEquiv` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The exact energy-zero label fibre is equivalent to Unit by the existing positive energy-zero characterization.

**Definition 1.15 (Actual energy-one label bijection).**

Lean statement: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.energyOneEquiv`

*Formalization.* `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.energyOneEquiv` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The all-charge energy-one label fibre is equivalent to Fin(rank), via proved charge exclusion.

**Definition 1.16 (All-charge energy-two label construction).**

Lean statement: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.energyTwoDecode`

*Formalization.* `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.energyTwoDecode` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Neutral oscillator labels and norm-four charged ground states construct actual energy-two labels.

**Definition 1.17 (All-charge energy-two sum decomposition).**

Lean statement: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.energyTwoEquiv`

*Formalization.* `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.energyTwoEquiv` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The decoder bijection identifies the actual energy-two fibre with OscillatorFiber(D,2) + NormFour(D).

**Definition 1.18 (Complete energy-two configurations).**

Lean statement: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.energyTwoConfigurations`

*Formalization.* `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.energyTwoConfigurations` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The actual label fibre is equivalent to (Fin(rank) + Sym(Fin(rank),2)) + NormFour(D), without duplication.

**Definition 1.19 (Reindexed existing actual-carrier basis).**

Lean statement: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.gradeTwoBasis`

*Formalization.* `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.gradeTwoBasis` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Reindex LatticeEnergyGrading.gradeBasis by the proved complete energy-two configurations; the carrier remains the actual lattice Fock carrier.

**Theorem 1.20 (Actual-carrier grade-two dimension).**

Lean statement: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.grade_two_finrank`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.grade_two_finrank` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The derived finite shell and reindexed basis yield rank + choose(rank+1,2) + Nat.card(NormFour(D)).

**Theorem 1.21 (Canonical inverse-Gram Sugawara low spectrum).**

Lean statement: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.actual_rootless_low_spectrum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.actual_rootless_low_spectrum` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every signed integer n the literal sugawaraMode(D,gramComplex(D) inverse,0) eigenspace at n is finite dimensional. Its dimensions at zero, one and two are 1, rank, and rank + choose(rank+1,2) + Nat.card(NormFour(D)).

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.NormFour`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.OscillatorFiber`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.actual_rootless_low_spectrum`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.chargeEnergy_gap`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.energyOneEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.energyTwoConfigurations`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.energyTwoDecode`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.energyTwoEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.energyZeroEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.energy_one_iff`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.energy_two_iff`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.gradeTwoBasis`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.grade_two_finrank`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.neutral_energy_two_card`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.normFour_finite`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.oscillatorOneEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.oscillatorTwoDecode`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.oscillatorTwoEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.oscillator_one_iff`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.oscillator_two_classification`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeRootlessLowGrades.pairOccupation`
- Dependency: [D5/S3/VertexAlgebra/LatticeActualLZeroGrading](LatticeActualLZeroGrading.md)
