# Cubic Theta Lattice Dissection

## Abstract

Finite Eisenstein norm fibres give a complete cubic lattice dissection.

The norm is Q(x,y)=x^2+xy+y^2 and the shifted exponent is e(x,y)=3Q(x,y)-2x-y. Every lattice point is included. The two theta series count complete finite fibres over the integers, and their monomial sums converge coefficientwise. These lattice series are not defined by Euler products.

**Definition 1.1 (Eisenstein norm).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaLattice.eisensteinNorm`

*Formalization.* `D5/S3/Arith/ModularForms/CubicThetaLattice.eisensteinNorm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The integer binary norm Q on all ordered integer pairs.

**Definition 1.2 (Three-core lattice exponent).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaLattice.coreExponent`

*Formalization.* `D5/S3/Arith/ModularForms/CubicThetaLattice.coreExponent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The integral shifted exponent 3Q(x,y)-2x-y in the source's three-core sum.

**Definition 1.3 (Norm fibres).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaLattice.NormFiber`

*Formalization.* `D5/S3/Arith/ModularForms/CubicThetaLattice.NormFiber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The complete integer-pair fibre of norm n, for each natural n.

**Definition 1.4 (Shifted fibres).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaLattice.CoreFiber`

*Formalization.* `D5/S3/Arith/ModularForms/CubicThetaLattice.CoreFiber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The complete integer-pair fibre of shifted exponent n.

**Theorem 1.5 (Coercivity).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaLattice.norm_coercive`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaLattice.norm_coercive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The exact identity 2Q=x^2+y^2+(x+y)^2 bounds both coordinates.

**Theorem 1.6 (Nonnegative norm).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaLattice.norm_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaLattice.norm_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The norm is nonnegative at every integer pair.

**Theorem 1.7 (Integral shifted norm).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaLattice.core_shift_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaLattice.core_shift_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

Q(3x-1,3y)=3e(x,y)+1. This retains the linear terms -2x-y exactly.

**Theorem 1.8 (Nonnegative shifted exponent).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaLattice.core_exponent_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaLattice.core_exponent_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

Integrality and the shifted norm identity imply e(x,y) is nonnegative.

**Definition 1.9 (Finite norm fibres).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaLattice.normFiber_finite`

*Formalization.* `D5/S3/Arith/ModularForms/CubicThetaLattice.normFiber_finite` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

Coercivity puts each norm fibre in an explicit finite integer rectangle.

**Definition 1.10 (Finite shifted fibres).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaLattice.coreFiber_finite`

*Formalization.* `D5/S3/Arith/ModularForms/CubicThetaLattice.coreFiber_finite` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The injective shift (x,y) to (3x-1,3y) embeds each shifted fibre into a finite norm fibre.

**Definition 1.11 (Norm theta series).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaLattice.normTheta`

*Formalization.* `D5/S3/Arith/ModularForms/CubicThetaLattice.normTheta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

Coefficient n is the rational image of the cardinality of the complete norm fibre.

**Definition 1.12 (Shifted theta series).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaLattice.coreTheta`

*Formalization.* `D5/S3/Arith/ModularForms/CubicThetaLattice.coreTheta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

Coefficient n is the rational image of the cardinality of the complete shifted fibre. No product identity is assumed.

**Theorem 1.13 (Zero shifted fibre).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaLattice.core_fiber_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaLattice.core_fiber_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The unique integer pair of shifted exponent zero is (0,0).

**Theorem 1.14 (Coefficient positivity and normalization).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaLattice.theta_nonnegative_and_normalized`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaLattice.theta_nonnegative_and_normalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

Both lattice series have nonnegative coefficients and constant coefficient one.

**Theorem 1.15 (Finite-fibre series).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaLattice.hasSum_counted_fibers`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaLattice.hasSum_counted_fibers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

For every nonnegative integer weight on the integer-pair lattice with finite fibres, the fibre-cardinality series is the full coefficientwise monomial sum.

**Theorem 1.16 (The full lattice sums).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaLattice.hasSum_lattice_theta`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaLattice.hasSum_lattice_theta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

For every topology on the rational coefficient field, both fibre series are the coefficientwise sums of all lattice monomials at their nonnegative integral exponents.

**Definition 1.17 (Norm-tripling equivalence).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaLattice.normTripleEquiv`

*Formalization.* `D5/S3/Arith/ModularForms/CubicThetaLattice.normTripleEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The map (x,y) to (x-y,x+2y) identifies norm-n and norm-3n fibres. The inverse uses the exact integer divisions (2u+v)/3 and (v-u)/3.

**Definition 1.18 (Six rotated core fibres).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaLattice.normCoreEquiv`

*Formalization.* `D5/S3/Arith/ModularForms/CubicThetaLattice.normCoreEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

All norm-(3n+1) points are uniquely obtained by one of six rotations of (3x-1,3y), with e(x,y)=n. Coordinate residues make the six images disjoint and exhaustive.

**Theorem 1.19 (All-index residue counts).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaLattice.norm_fiber_residue_counts`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaLattice.norm_fiber_residue_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The norm-fibre counts at 3n, 3n+1 and 3n+2 are respectively the norm-n count, six times the shifted-n count, and zero. The variable n is unrestricted.

**Theorem 1.20 (Cubic lattice dissection).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaLattice.norm_theta_dissection`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaLattice.norm_theta_dissection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The complete formal power-series identity A(X)=A(X^3)+6X T_lattice(X^3) follows from the fibre equivalences and exact PowerSeries.expand coefficients. It includes degree zero.

**Theorem 1.21 (Norm residues).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaLattice.norm_mod_three`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaLattice.norm_mod_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The Eisenstein norm has only residues zero and one modulo three, detected by the coordinate difference.

**Theorem 1.22 (Cubic phases of the six cosets).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaLattice.normCoreEquiv_coordinate_residue`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaLattice.normCoreEquiv_coordinate_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The six complete rotated core cosets have alternating nontrivial cubic phases.

This module supplies complete lattice counts. CubicThetaCoreProduct identifies the actual Euler quotient, CubicThetaIdentities proves the two other classical relations, and EtaSignK6 proves the full normalized sign theorem. This classical lattice mathematics carries no literature priority, unique, independent acceptance or KPI claim.

## References

- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaLattice.CoreFiber`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaLattice.NormFiber`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaLattice.coreExponent`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaLattice.coreFiber_finite`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaLattice.coreTheta`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaLattice.core_exponent_nonneg`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaLattice.core_fiber_zero`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaLattice.core_shift_norm`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaLattice.eisensteinNorm`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaLattice.hasSum_counted_fibers`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaLattice.hasSum_lattice_theta`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaLattice.normCoreEquiv`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaLattice.normCoreEquiv_coordinate_residue`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaLattice.normFiber_finite`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaLattice.normTheta`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaLattice.normTripleEquiv`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaLattice.norm_coercive`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaLattice.norm_fiber_residue_counts`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaLattice.norm_mod_three`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaLattice.norm_nonneg`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaLattice.norm_theta_dissection`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaLattice.theta_nonnegative_and_normalized`
