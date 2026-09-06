# Ququint Certificate Geometry Bridge

## Abstract

The numerical certificate data are the actual ququint tangent forms.

**Definition 1.1 (The complex tangent basis).**

$$\forall i:\mathrm{Fin} 5,\forall j:\mathrm{Fin} 4,\mathrm{complexBasis}(i,j)=\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{phases}(i)\cdot\mathrm{Complex}.\mathrm{mk}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{basisMatrix}(\mathrm{Fin}.\mathrm{castAdd}(5,i),j),\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{basisMatrix}(\mathrm{Fin}.\mathrm{natAdd}(5,i),j))$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateBridge.complexBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

complexBasis has type Matrix (Fin 5) (Fin 4) C. The two real halves of basisMatrix become the real and imaginary components before phase multiplication.

**Definition 1.2 (The real pullback matrix).**

$$\forall m:\mathrm{Matrix}(\mathrm{Fin} 5,\mathrm{Fin} 5,\mathbb{C}),\forall i j:\mathrm{Fin} 4,\mathrm{pullback}(m,i,j)=\mathrm{Complex}.\mathrm{re}(\mathrm{dotProduct}(\mathrm{star}(((k:\mathrm{Fin} 5)\mapsto\mathrm{complexBasis}(k,i))),\mathrm{Matrix}.\mathrm{mulVec}(m,((k:\mathrm{Fin} 5)\mapsto\mathrm{complexBasis}(k,j)))))/5$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateBridge.pullback` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The pullback has type Matrix (Fin 4) (Fin 4) R. This expression defines each entry.

**Definition 1.3 (The pulled-back phase-point form).**

$$\forall q p:\mathrm{Fin} 5,\mathrm{phaseForm}(q,p)=\mathrm{pullback}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{phasePoint}(q,p))$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateBridge.phaseForm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each phaseForm is a four-by-four real matrix obtained by the displayed pullback definition.

**Definition 1.4 (The coordinate Gram matrix).**

$$\mathrm{gram}:\mathrm{Matrix}(\mathrm{Fin} 4,\mathrm{Fin} 4,\mathbb{R})=[[10-\mathrm{radical}^{2}/2,10-3\cdot\mathrm{radical}^{2}/4,\mathrm{radical}^{3}/4-3\cdot\mathrm{radical},-\mathrm{radical}^{3}/8+5\cdot\mathrm{radical}/2],[10-3\cdot\mathrm{radical}^{2}/4,10-\mathrm{radical}^{2}/2,\mathrm{radical}^{3}/8-5\cdot\mathrm{radical}/2,-\mathrm{radical}^{3}/4+3\cdot\mathrm{radical}],[\mathrm{radical}^{3}/4-3\cdot\mathrm{radical},\mathrm{radical}^{3}/8-5\cdot\mathrm{radical}/2,7\cdot\mathrm{radical}^{2}/10+2,31\cdot\mathrm{radical}^{2}/20-12],[-\mathrm{radical}^{3}/8+5\cdot\mathrm{radical}/2,-\mathrm{radical}^{3}/4+3\cdot\mathrm{radical},31\cdot\mathrm{radical}^{2}/20-12,7\cdot\mathrm{radical}^{2}/10+2]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateBridge.gram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix is displayed as a vector of rows, with radical from QuquintCertificateData. The public identity gram_eq below identifies this table with the real matrix product.

**Definition 1.5 (The complete Wigner sign table).**

$$\mathrm{signs}:\mathrm{Matrix}(\mathrm{Fin} 5,\mathrm{Fin} 5,\mathrm{SignType})=[[-1,1,1,0,1],[-1,1,1,0,1],[1,-1,1,1,0],[1,0,1,-1,1],[1,-1,1,1,0]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateBridge.signs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Rows are indexed by q and columns by p. signs_eq proves agreement with SignType.sign.

**Definition 1.6 (The ordered zero-point enumeration).**

$$\mathrm{zeroIndex}:\mathrm{Fin} 5\to(\mathrm{Fin} 5\times\mathrm{Fin} 5)=[(0,3),(1,3),(2,4),(3,1),(4,4)]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateBridge.zeroIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The order is the same as the five entries of QuquintCertificateData.zeroQ.

**Definition 1.7 (The real and imaginary blocks).**

$$\forall m:\mathrm{Matrix}(\mathrm{Fin} 5,\mathrm{Fin} 5,\mathbb{C}),\forall i j:\mathrm{Fin} 10,\mathrm{realification}(m,i,j)=\mathrm{Fin}.\mathrm{addCases}(((x:\mathrm{Fin} 5)\mapsto\mathrm{Fin}.\mathrm{addCases}(((y:\mathrm{Fin} 5)\mapsto\mathrm{Complex}.\mathrm{re}(m(x,y))),((y:\mathrm{Fin} 5)\mapsto-\mathrm{Complex}.\mathrm{im}(m(x,y))),j)),((x:\mathrm{Fin} 5)\mapsto\mathrm{Fin}.\mathrm{addCases}(((y:\mathrm{Fin} 5)\mapsto\mathrm{Complex}.\mathrm{im}(m(x,y))),((y:\mathrm{Fin} 5)\mapsto\mathrm{Complex}.\mathrm{re}(m(x,y))),j)),i)$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateBridge.realification` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The resulting Matrix (Fin 10) (Fin 10) R has blocks [Re, -Im; Im, Re]. Fin.addCases fixes the real-first, imaginary-second order on each axis.

**Theorem 1.8 (Zero form at the first point).**

$$\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{zeroQ}(0)=\mathrm{phaseForm}(0,3)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateBridge.zeroQ_0_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact entrywise arithmetic verifies the first numerical zero form.

**Theorem 1.9 (Zero form at the second point).**

$$\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{zeroQ}(1)=\mathrm{phaseForm}(1,3)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateBridge.zeroQ_1_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact entrywise arithmetic verifies the second numerical zero form.

**Theorem 1.10 (Zero form at the third point).**

$$\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{zeroQ}(2)=\mathrm{phaseForm}(2,4)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateBridge.zeroQ_2_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact entrywise arithmetic verifies the third numerical zero form.

**Theorem 1.11 (Zero form at the fourth point).**

$$\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{zeroQ}(3)=\mathrm{phaseForm}(3,1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateBridge.zeroQ_3_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact entrywise arithmetic verifies the fourth numerical zero form.

**Theorem 1.12 (Zero form at the fifth point).**

$$\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{zeroQ}(4)=\mathrm{phaseForm}(4,4)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateBridge.zeroQ_4_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact entrywise arithmetic verifies the fifth numerical zero form.

complexBasis applies the component phases to the real and imaginary halves of basisMatrix. pullback is the real part of the resulting complex matrix contraction divided by five; phaseForm applies it to phasePoint. realification uses the real blocks Re, -Im, Im, Re in that order. All imported declarations in the formulas retain their full Lean namespaces.

**Theorem 1.13 (The same tangent coordinates).**

$$\forall a:(\mathrm{Fin} 4\to\mathbb{R}),\mathrm{Matrix}.\mathrm{mulVec}(\mathrm{complexBasis},((i:\mathrm{Fin} 4)\mapsto(a(i):\mathbb{C})))=\mathrm{WithLp}.\mathrm{ofLp}((\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{tangentEquiv}(a):\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{State}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateBridge.complexBasis_tangentEquiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The columns give exactly the public real linear equivalence onto tangent.

**Theorem 1.14 (Literal phase-point realification).**

$$\forall q p:\mathrm{Fin} 5,\mathrm{phaseForm}(q,p)=1/5\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{basisMatrix})\cdot\mathrm{realification}(\mathrm{Matrix}.\mathrm{conjTranspose}(\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{phases}))\cdot\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{phasePoint}(q,p)\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{phases}))\cdot\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{basisMatrix}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateBridge.phaseForm_realification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Diagonal conjugation and the realification blocks give the stated identity for every phase point.

**Theorem 1.15 (The numerical Gram matrix).**

$$\mathrm{gram}=\mathrm{Matrix}.\mathrm{transpose}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{basisMatrix})\cdot\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{basisMatrix}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateBridge.gram_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every entry of the explicit numerical gram matrix is checked against this product.

**Theorem 1.16 (The numerical sign table).**

$$\forall q p:\mathrm{Fin} 5,\mathrm{signs}(q,p)=\mathrm{SignType}.\mathrm{sign}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{wigner}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{psi},q,p))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateBridge.signs_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal twenty-five-entry sign table agrees with the signs of the Wigner values, including all zeros.

**Theorem 1.17 (Exactly the vanishing points).**

$$\mathrm{Finset}.\mathrm{image}(\mathrm{zeroIndex},\mathrm{Finset}.\mathrm{univ})=\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{zeroPoints}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateBridge.zeroIndex_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

zeroIndex enumerates (0,3), (1,3), (2,4), (3,1), (4,4) in the order of the numerical data.

**Theorem 1.18 (All five numerical zero forms).**

$$\forall i:\mathrm{Fin} 5,\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{zeroQ}(i)=\mathrm{phaseForm}((\mathrm{zeroIndex}(i)).1,(\mathrm{zeroIndex}(i)).2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateBridge.zeroQ_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The five named entrywise computations zeroQ_0_eq through zeroQ_4_eq establish this enumeration identity.

**Theorem 1.19 (The numerical base matrix).**

$$\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{base}=\mathrm{pullback}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{gradient})-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{lOne}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{psi})\cdot\mathrm{gram}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateBridge.base_eq_gradient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact quartic-field arithmetic identifies all sixteen entries, including the subtracted norm term.

**Theorem 1.20 (The actual nonzero sign contribution).**

$$\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{base}=(\sum_{qp \in (\mathrm{Finset}.\mathrm{univ}\setminus\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{zeroPoints})}(\mathrm{SignType}.\mathrm{sign}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{wigner}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{psi},qp.1,qp.2)):\mathbb{R})\cdot\mathrm{phaseForm}(qp.1,qp.2))-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{lOne}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{psi})\cdot\mathrm{gram}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateBridge.base_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The base is the signed sum over exactly the nonzero points, minus lOne of psi times gram.

**Theorem 1.21 (Evaluation through tangentEquiv).**

$$\forall q p:\mathrm{Fin} 5,\forall a:(\mathrm{Fin} 4\to\mathbb{R}),\mathrm{dotProduct}(a,\mathrm{Matrix}.\mathrm{mulVec}(\mathrm{phaseForm}(q,p),a))=\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{wigner}((\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{tangentEquiv}(a):\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{State}),q,p)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateBridge.phaseForm_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Contracting the real matrix computes the Wigner quadratic form of the actual tangent vector.

**Theorem 1.22 (Evaluation of the squared norm).**

$$\forall a:(\mathrm{Fin} 4\to\mathbb{R}),\mathrm{dotProduct}(a,\mathrm{Matrix}.\mathrm{mulVec}(\mathrm{gram},a))=\mathrm{Norm}.\mathrm{norm}((\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{tangentEquiv}(a):\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{State}))^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateBridge.gram_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each component phase has norm one, so the real Gram contraction is the squared norm in State.

This module proves only the identification of the certificate data with the ququint geometry. QuquintFiniteMaximum uses the bridge for the finite sign maximum and negativity equivalence. The normalized perturbation identity and strict mana decrease are proved in QuquintStrictDecrease.exact_change and QuquintStrictDecrease.directional_decrease for the constrained tangent family. It makes no claim about general mana extremisation, other dimensions or critical points, author-verbatim Claim C, or global novelty.

## References

- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateBridge.base_eq`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateBridge.base_eq_gradient`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateBridge.complexBasis`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateBridge.complexBasis_tangentEquiv`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateBridge.gram`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateBridge.gram_eq`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateBridge.gram_eval`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateBridge.phaseForm`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateBridge.phaseForm_eval`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateBridge.phaseForm_realification`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateBridge.pullback`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateBridge.realification`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateBridge.signs`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateBridge.signs_eq`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateBridge.zeroIndex`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateBridge.zeroIndex_image`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateBridge.zeroQ_0_eq`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateBridge.zeroQ_1_eq`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateBridge.zeroQ_2_eq`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateBridge.zeroQ_3_eq`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateBridge.zeroQ_4_eq`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateBridge.zeroQ_eq`
- Dependency: [D5/S3/Quantum/Magic/QuquintCertificateData](QuquintCertificateData.md)
- Dependency: [D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry](QuquintWignerCriticalGeometry.md)
