# Ququint Wigner Critical Geometry

## Abstract

Exact ququint Wigner zeros, tangent dimension, and critical gradient.

**Definition 1.1 (The state space).**

$$\mathrm{State}=\mathrm{EuclideanSpace}(\mathbb{C},\mathrm{Fin} 5)$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.State` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

State is the complex Euclidean space on Fin 5, with its L2 norm.

**Definition 1.2 (The positive radical).**

$$\mathrm{radical}=\sqrt{10+2\cdot\sqrt{5}}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.radical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All exact coordinate entries use this positive real square root.

**Definition 1.3 (The fifth root of unity).**

$$\mathrm{zeta}=\mathrm{Complex}.\mathrm{exp}(2\cdot(\mathrm{Real}.\mathrm{pi}:\mathbb{C})\cdot\mathrm{Complex}.\mathrm{I}/5)$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.zeta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The phase convention uses exp of two pi times the imaginary unit divided by five.

**Definition 1.4 (The phase-point kernel).**

$$\forall q p x y:\mathrm{Fin} 5,\mathrm{phasePoint}(q,p,x,y)=\mathrm{ite}((x:\mathrm{ZMod}(5))+(y:\mathrm{ZMod}(5)) = 2\cdot(q:\mathrm{ZMod}(5)),\mathrm{zeta}^{\mathrm{val}((p:\mathrm{ZMod}(5))\cdot((x:\mathrm{ZMod}(5))-(y:\mathrm{ZMod}(5))))},0)$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.phasePoint` (`✓ std3`).

*Citation.* Muhammad Erew and Moshe Goldstein (2025). *Extremizing Measures of Magic on Pure States by Clifford-stabilizer States*. DOI: [10.48550/arXiv.2512.19657](https://doi.org/10.48550/arXiv.2512.19657).

*Commentary.*

The condition and exponent arithmetic are in ZMod 5. val converts the exponent to a natural number. This is the paper's phase-point convention after exchanging the labels p and q.

**Definition 1.5 (The Wigner quadratic form).**

$$\forall v:\mathrm{State},\forall q p:\mathrm{Fin} 5,\mathrm{wigner}(v,q,p)=\mathrm{Complex}.\mathrm{re}(\mathrm{dotProduct}(\mathrm{star}(\mathrm{WithLp}.\mathrm{ofLp}(v)),\mathrm{Matrix}.\mathrm{mulVec}(\mathrm{phasePoint}(q,p),\mathrm{WithLp}.\mathrm{ofLp}(v))))/5$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.wigner` (`✓ std3`).

*Citation.* Muhammad Erew and Moshe Goldstein (2025). *Extremizing Measures of Magic on Pure States by Clifford-stabilizer States*. DOI: [10.48550/arXiv.2512.19657](https://doi.org/10.48550/arXiv.2512.19657).

*Commentary.*

The real part of the Hermitian phase-point pairing is divided by five.

**Definition 1.6 (The Wigner norm sum).**

$$\forall v:\mathrm{State},\mathrm{lOne}(v)=\sum_{q:\mathrm{Fin} 5}\sum_{p:\mathrm{Fin} 5}\mathrm{abs}(\mathrm{wigner}(v,q,p))$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.lOne` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two finite sums include all twenty-five phase points.

**Definition 1.7 (The specified ququint state).**

$$\mathrm{psi}=\mathrm{WithLp}.\mathrm{toLp}(2,(1/(\sqrt{5}:\mathbb{C}))\cdot[1,1,\mathrm{zeta}^{3},1,\mathrm{zeta}^{2}])$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.psi` (`✓ std3`).

*Citation.* Muhammad Erew and Moshe Goldstein (2025). *Extremizing Measures of Magic on Pure States by Clifford-stabilizer States*. DOI: [10.48550/arXiv.2512.19657](https://doi.org/10.48550/arXiv.2512.19657).

*Commentary.*

Appendix E, equation E.3a, specifies this normalized five-component state.

**Definition 1.8 (The vanishing phase points).**

$$\mathrm{zeroPoints}=\mathrm{Finset}.\mathrm{filter}(((qp:(\mathrm{Fin} 5\times\mathrm{Fin} 5))\mapsto\mathrm{wigner}(\mathrm{psi},(qp).1,(qp).2) = 0),\mathrm{Finset}.\mathrm{univ})$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.zeroPoints` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Filtering the finite phase plane by the vanishing predicate defines zeroPoints.

**Theorem 1.9 (The exact zero set).**

$$\mathrm{zeroPoints}=\left\{(0,3), (1,3), (2,4), (3,1), (4,4)\right\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.zero_points_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact Wigner table determines these five points.

**Theorem 1.10 (The zero-set cardinality).**

$$\mathrm{Finset}.\mathrm{card}(\mathrm{zeroPoints})=5$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.zero_points_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The five displayed points are distinct.

**Theorem 1.11 (The norm sum at the specified state).**

$$\mathrm{lOne}(\mathrm{psi})=1+2\cdot\sqrt{5}/5$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.lOne_psi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact twenty-five-entry Wigner table gives this value.

**Definition 1.12 (The signed phase-point sum).**

$$\mathrm{gradient}=\sum_{q:\mathrm{Fin} 5}\sum_{p:\mathrm{Fin} 5}(\mathrm{SignType}.\mathrm{sign}(\mathrm{wigner}(\mathrm{psi},q,p)):\mathbb{C})\cdot\mathrm{phasePoint}(q,p)$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.gradient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The SignType coefficient is explicitly coerced to the complex scalar field.

**Definition 1.13 (The constrained real tangent space).**

$$\forall v:\mathrm{State},v \in \mathrm{tangent}\iff(\mathrm{dotProduct}(\mathrm{star}(\mathrm{WithLp}.\mathrm{ofLp}(\mathrm{psi})),\mathrm{WithLp}.\mathrm{ofLp}(v)) = 0 \land (\forall qp:(\mathrm{Fin} 5\times\mathrm{Fin} 5),qp \in \mathrm{zeroPoints}\implies\mathrm{Complex}.\mathrm{re}(\mathrm{dotProduct}(\mathrm{star}(\mathrm{WithLp}.\mathrm{ofLp}(\mathrm{psi})),\mathrm{Matrix}.\mathrm{mulVec}(\mathrm{phasePoint}((qp).1,(qp).2),\mathrm{WithLp}.\mathrm{ofLp}(v)))) = 0))$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.tangent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

tangent is the real Submodule of State cut out by complex orthogonality to psi and the five real phase-point pairing constraints.

**Definition 1.14 (The component phases).**

$$\mathrm{phases}=[1,1,\mathrm{zeta}^{3},1,\mathrm{zeta}^{2}]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.phases` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This vector has type Fin 5 to the complex numbers.

**Definition 1.15 (Phase-adjusted real coordinates).**

$$\forall u:(\mathrm{Fin} 10\to\mathbb{R}),\mathrm{gauge}(u)=\mathrm{WithLp}.\mathrm{toLp}(2,((i:\mathrm{Fin} 5)\mapsto\mathrm{phases}(i)\cdot\mathrm{Complex}.\mathrm{mk}(u(\mathrm{Fin}.\mathrm{castAdd}(5,i)),u(\mathrm{Fin}.\mathrm{natAdd}(5,i)))))$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.gauge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first five real coordinates and the last five imaginary coordinates are multiplied by phases.

**Definition 1.16 (The exact real basis matrix).**

$$\mathrm{basisMatrix}:\mathrm{Matrix}(\mathrm{Fin} 10,\mathrm{Fin} 4,\mathbb{R})=[[-1,\mathrm{radical}^{2}/4-3,-\mathrm{radical}^{3}/10+\mathrm{radical},-\mathrm{radical}^{3}/40],[3-\mathrm{radical}^{2}/4,3-\mathrm{radical}^{2}/4,3\cdot\mathrm{radical}^{3}/40-\mathrm{radical},-3\cdot\mathrm{radical}^{3}/40+\mathrm{radical}],[\mathrm{radical}^{2}/4-3,-1,\mathrm{radical}^{3}/40,\mathrm{radical}^{3}/10-\mathrm{radical}],[1,0,0,0],[0,1,0,0],[0,0,-1,2-\mathrm{radical}^{2}/4],[0,0,\mathrm{radical}^{2}/4-2,\mathrm{radical}^{2}/4-2],[0,0,2-\mathrm{radical}^{2}/4,-1],[0,0,1,0],[0,0,0,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.basisMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ten rows are listed in the real-then-imaginary order used by gauge. The checked constraint, selector, and elimination identities establish a basis of tangent.

**Definition 1.17 (The real linear coordinate equivalence).**

$$\mathrm{tangentEquiv}:(\mathrm{Fin} 4\to\mathbb{R})\equiv_{\mathrm{l}}[\mathbb{R}]\mathrm{tangent},(\forall a:(\mathrm{Fin} 4\to\mathbb{R}),(\mathrm{tangentEquiv}(a):\mathrm{State})=\mathrm{gauge}(\mathrm{Matrix}.\mathrm{mulVec}(\mathrm{basisMatrix},a))) \land (\forall v:\mathrm{tangent},\mathrm{tangentEquiv}.\mathrm{symm}(v)=[\mathrm{Complex}.\mathrm{re}(\mathrm{WithLp}.\mathrm{ofLp}((v:\mathrm{State}))(3)/\mathrm{phases}(3)),\mathrm{Complex}.\mathrm{re}(\mathrm{WithLp}.\mathrm{ofLp}((v:\mathrm{State}))(4)/\mathrm{phases}(4)),\mathrm{Complex}.\mathrm{im}(\mathrm{WithLp}.\mathrm{ofLp}((v:\mathrm{State}))(3)/\mathrm{phases}(3)),\mathrm{Complex}.\mathrm{im}(\mathrm{WithLp}.\mathrm{ofLp}((v:\mathrm{State}))(4)/\mathrm{phases}(4))])$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.tangentEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward map carries the displayed state into tangent. The inverse removes the phases and takes real coordinates 3 and 4 and imaginary coordinates 3 and 4; both inverse laws are proved.

**Theorem 1.18 (The tangent dimension).**

$$\mathrm{Module}.\mathrm{finrank}(\mathbb{R},\mathrm{tangent})=4$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.tangent_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real linear equivalence gives dimension four.

**Theorem 1.19 (Restriction to the nonzero Wigner points).**

$$\mathrm{gradient}=\sum_{qp \in (\mathrm{Finset}.\mathrm{univ}\setminus\mathrm{zeroPoints})}(\mathrm{SignType}.\mathrm{sign}(\mathrm{wigner}(\mathrm{psi},(qp).1,(qp).2)):\mathbb{C})\cdot\mathrm{phasePoint}((qp).1,(qp).2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.gradient_restricted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The terms omitted from the full gradient sum have zero SignType coefficient.

Names below are the public Lean names in D5.S3.Quantum.Magic.QuquintWignerCriticalGeometry. zeta is the fifth root of unity used in psi and phasePoint. wigner is the real phase-point quadratic form divided by five; lOne sums the absolute values of its twenty-five entries.

zeroPoints is the set of vanishing Wigner entries of psi. tangent imposes complex orthogonality to psi and vanishing real phase-point pairings at every point of zeroPoints.

**Theorem 1.20 (Exact zero set and dimension).**

$$\mathrm{zeroPoints}=\{(0,3),(1,3),(2,4),(3,1),(4,4)\} \land \mathrm{Finset}.\mathrm{card}(\mathrm{zeroPoints})=5 \land \mathrm{Module}.\mathrm{finrank}(\mathbb{R},\mathrm{tangent})=4 \land \mathrm{lOne}(\mathrm{psi})=1+2\sqrt{5}/5$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.critical_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Muhammad Erew and Moshe Goldstein (2025). *Extremizing Measures of Magic on Pure States by Clifford-stabilizer States*. DOI: [10.48550/arXiv.2512.19657](https://doi.org/10.48550/arXiv.2512.19657).

*Commentary.*

The exact Wigner table is evaluated using radical. The public real linear equivalence tangentEquiv gives four real coordinates on tangent. Its inverse removes the component phases and selects four real coordinates. Checked matrix identities establish both inverse laws for the original constraint subspace.

**Theorem 1.21 (Critical gradient).**

$$\mathrm{Matrix}.\mathrm{mulVec}(\mathrm{gradient},\mathrm{WithLp}.\mathrm{ofLp}(\mathrm{psi}))=(5\cdot\mathrm{lOne}(\mathrm{psi}):\mathbb{C})\cdot\mathrm{WithLp}.\mathrm{ofLp}(\mathrm{psi})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.gradient_psi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Muhammad Erew and Moshe Goldstein (2025). *Extremizing Measures of Magic on Pure States by Clifford-stabilizer States*. DOI: [10.48550/arXiv.2512.19657](https://doi.org/10.48550/arXiv.2512.19657).

*Commentary.*

gradient is the sum of phasePoint matrices weighted by SignType.sign of the Wigner entries of psi. The public gradient_restricted identity identifies this restricted sum with gradient, whose definition includes all points and has zero coefficients on zeroPoints.

**Theorem 1.22 (Vanishing first variation).**

$$\forall v:\mathrm{tangent},\mathrm{HasDerivAt}(((e:\mathbb{R})\mapsto \mathrm{lOne}(\mathrm{psi}+e\cdot(v:\mathrm{State}))),0,0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.first_variation_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Muhammad Erew and Moshe Goldstein (2025). *Extremizing Measures of Magic on Pure States by Clifford-stabilizer States*. DOI: [10.48550/arXiv.2512.19657](https://doi.org/10.48550/arXiv.2512.19657).

*Commentary.*

The Lean statement is HasDerivAt with derivative zero, for every vector in tangent. Hermitian symmetry gives an exact quadratic expansion of each Wigner entry. On zeroPoints the linear coefficient vanishes. At the other points the derivative of absolute value multiplies the coefficient by its sign, and the gradient identity and orthogonality to psi make their sum zero.

**Theorem 1.23 (Exact Wigner expansion).**

$$\forall v:\mathrm{State},\forall q p:\mathrm{Fin} 5,\forall e:\mathbb{R},\mathrm{wigner}(\mathrm{psi}+e\cdot v,q,p)=\mathrm{wigner}(\mathrm{psi},q,p)+e\cdot(2\cdot\mathrm{Complex}.\mathrm{re}(\mathrm{dotProduct}(\mathrm{star}(\mathrm{WithLp}.\mathrm{ofLp}(\mathrm{psi})),\mathrm{Matrix}.\mathrm{mulVec}(\mathrm{phasePoint}(q,p),\mathrm{WithLp}.\mathrm{ofLp}(v))))/5)+e^{2}\cdot\mathrm{wigner}(v,q,p)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.wigner_expand` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This existing expansion is now public for normalized perturbations. The proof uses the Hermitian phase-point pairings and real scalar multiplication.

**Theorem 1.24 (Cancellation of the linear sum).**

$$\forall v:\mathrm{tangent},\sum_{q:\mathrm{Fin} 5}\sum_{p:\mathrm{Fin} 5}(\mathrm{SignType}.\mathrm{sign}(\mathrm{wigner}(\mathrm{psi},q,p)):\mathbb{R})\cdot(2\cdot\mathrm{Complex}.\mathrm{re}(\mathrm{dotProduct}(\mathrm{star}(\mathrm{WithLp}.\mathrm{ofLp}(\mathrm{psi})),\mathrm{Matrix}.\mathrm{mulVec}(\mathrm{phasePoint}(q,p),\mathrm{WithLp}.\mathrm{ofLp}((v:\mathrm{State})))))/5)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.first_coefficient_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

gradient_psi, Hermitian symmetry, and the complex orthogonality in tangent prove this exact cancellation. QuquintStrictDecrease uses this equality when summing its locally valid absolute-value expansions.

Scope: this module concerns this state in dimension five. It does not claim a general solution of mana extremisation, results in other dimensions or at other critical points, that Claim C is the authors' verbatim conjecture, or global novelty beyond the recorded search. The normalized direction result is developed in QuquintStrictDecrease.

## References

- Truth anchor: `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.State`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.basisMatrix`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.critical_geometry`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.first_coefficient_zero`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.first_variation_zero`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.gauge`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.gradient`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.gradient_psi`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.gradient_restricted`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.lOne`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.lOne_psi`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.phasePoint`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.phases`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.psi`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.radical`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.tangent`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.tangentEquiv`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.tangent_finrank`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.wigner`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.wigner_expand`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.zeroPoints`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.zero_points_card`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.zero_points_eq`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry.zeta`
- Dependency: [D5/S3/Constants/PentagonCosines](../../Constants/PentagonCosines.md)
