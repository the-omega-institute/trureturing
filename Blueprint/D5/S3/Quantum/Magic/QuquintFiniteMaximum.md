# Ququint Finite Sign Maximum

## Abstract

The constrained second variation is exactly the maximum of the thirty-two branch forms.

**Definition 1.1 (The five bits of a branch).**

$$\forall s:\mathrm{Fin} 32,\forall i:\mathrm{Fin} 5,\mathrm{signPattern}(s,i)=\mathrm{decide}(\mathrm{Nat}.\mathrm{mod}(\mathrm{Nat}.\mathrm{div}(\mathrm{val}(s),2^{4-\mathrm{val}(i)}),2) \ne 0)$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintFiniteMaximum.signPattern` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

signPattern returns Bool. Nat.div is natural-number quotient and Nat.mod is remainder; the exponent uses natural subtraction. Index zero selects the highest of the five bits.

**Definition 1.2 (The real sign coefficient).**

$$\forall s:\mathrm{Fin} 32,\forall i:\mathrm{Fin} 5,\mathrm{signValue}(s,i)=\mathrm{ite}(\mathrm{signPattern}(s,i),1,-1)$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintFiniteMaximum.signValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real coefficient is one when the Boolean signPattern is true and minus one otherwise.

**Definition 1.3 (The complete integer witness table).**

$$\mathrm{integerWitness}:\mathrm{Fin} 32\to(\mathrm{Fin} 4\to\mathbb{Z}),\forall s:\mathrm{Fin} 32,\mathrm{integerWitness}(s)=[[-4,0,4,1],[-3,4,-1,4],[-4,-1,-2,4],[-4,2,-1,3],[-4,-1,0,4],[-2,-3,-4,4],[-4,-3,-2,4],[-3,4,4,-2],[-4,-4,4,-4],[-3,-4,3,-4],[-4,-3,4,-3],[-4,2,1,1],[-4,-3,4,-4],[-4,-4,3,-4],[-4,-2,2,-1],[-4,-3,3,-3],[-3,-1,-4,2],[-4,-3,-4,3],[-4,-1,-4,4],[-4,-2,-4,4],[-4,-4,-4,-4],[-4,-4,-4,-1],[-4,-4,-2,4],[-4,-4,-4,3],[-3,-4,4,-4],[-2,-4,1,-3],[-4,-4,4,-3],[-4,1,-2,2],[-4,-4,-2,-4],[-4,-4,-2,-3],[-4,-4,0,1],[-4,-4,-1,1]](s)$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintFiniteMaximum.integerWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The outer vector is indexed by s in Fin 32, starting at zero, and each row by Fin 4. These are all thirty-two integer cases in the Lean definition; its default case is the last row, because the input lies in Fin 32.

**Definition 1.4 (The second variation expression).**

$$\forall v:\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{State},\mathrm{secondVariation}(v)=(\sum_{qp \in (\mathrm{Finset}.\mathrm{univ}\setminus\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{zeroPoints})}(\mathrm{SignType}.\mathrm{sign}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{wigner}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{psi},(qp).1,(qp).2)):\mathbb{R})\cdot\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{wigner}(v,(qp).1,(qp).2))+(\sum_{qp \in \mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{zeroPoints}}\mathrm{abs}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{wigner}(v,(qp).1,(qp).2)))-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{lOne}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{psi})\cdot\mathrm{Norm}.\mathrm{norm}(v)^{2}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintFiniteMaximum.secondVariation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This definition includes the signed nonzero contribution, the five absolute values, and the subtracted squared norm term.

**Definition 1.5 (The finite maximum).**

$$\forall a:(\mathrm{Fin} 4\to\mathbb{R}),\mathrm{branchMaximum}(a)=\mathrm{max}_{s:\mathrm{Fin} 32}\mathrm{dotProduct}(a,\mathrm{Matrix}.\mathrm{mulVec}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(s),a))$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintFiniteMaximum.branchMaximum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The maximum is Finset.univ.sup' over the nonempty finite type Fin 32.

**Theorem 1.6 (Evaluation of each branch).**

$$\forall s:\mathrm{Fin} 32,\forall a:(\mathrm{Fin} 4\to\mathbb{R}),\mathrm{dotProduct}(a,\mathrm{Matrix}.\mathrm{mulVec}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(s),a))=\mathrm{dotProduct}(a,\mathrm{Matrix}.\mathrm{mulVec}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{base},a))+\sum_{i:\mathrm{Fin} 5}\mathrm{signValue}(s,i)\cdot\mathrm{dotProduct}(a,\mathrm{Matrix}.\mathrm{mulVec}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{zeroQ}(i),a))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintFiniteMaximum.branch_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient signValue is one for a set bit and minus one for an unset bit, using the same most-significant-bit-first order as branch.

**Theorem 1.7 (The absolute values in tangent coordinates).**

$$\forall a:(\mathrm{Fin} 4\to\mathbb{R}),\mathrm{secondVariation}((\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{tangentEquiv}(a):\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{State}))=\mathrm{dotProduct}(a,\mathrm{Matrix}.\mathrm{mulVec}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{base},a))+\sum_{i:\mathrm{Fin} 5}\mathrm{abs}(\mathrm{dotProduct}(a,\mathrm{Matrix}.\mathrm{mulVec}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{zeroQ}(i),a)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintFiniteMaximum.secondVariation_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bridge evaluates base, zeroQ and gram on the actual tangent vector.

**Theorem 1.8 (Exact sign maximum in coordinates).**

$$\forall a:(\mathrm{Fin} 4\to\mathbb{R}),(\sum_{qp \in (\mathrm{Finset}.\mathrm{univ}\setminus\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{zeroPoints})}(\mathrm{SignType}.\mathrm{sign}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{wigner}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{psi},(qp).1,(qp).2)):\mathbb{R})\cdot\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{wigner}((\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{tangentEquiv}(a):\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{State}),(qp).1,(qp).2))+(\sum_{qp \in \mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{zeroPoints}}\mathrm{abs}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{wigner}((\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{tangentEquiv}(a):\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{State}),(qp).1,(qp).2)))-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{lOne}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{psi})\cdot\mathrm{Norm}.\mathrm{norm}((\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{tangentEquiv}(a):\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{State}))^{2}=\mathrm{max}_{s:\mathrm{Fin} 32}\mathrm{dotProduct}(a,\mathrm{Matrix}.\mathrm{mulVec}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(s),a))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintFiniteMaximum.finite_sign_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each real coordinate vector, choose the five signs of its zero-point values. The resulting branch equals the sum of absolute values; every other branch is at most it.

**Theorem 1.9 (Exact sign maximum on the tangent subspace).**

$$\forall v:\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{tangent},(\sum_{qp \in (\mathrm{Finset}.\mathrm{univ}\setminus\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{zeroPoints})}(\mathrm{SignType}.\mathrm{sign}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{wigner}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{psi},(qp).1,(qp).2)):\mathbb{R})\cdot\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{wigner}((v:\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{State}),(qp).1,(qp).2))+(\sum_{qp \in \mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{zeroPoints}}\mathrm{abs}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{wigner}((v:\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{State}),(qp).1,(qp).2)))-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{lOne}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{psi})\cdot\mathrm{Norm}.\mathrm{norm}((v:\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{State}))^{2}=\mathrm{max}_{s:\mathrm{Fin} 32}\mathrm{dotProduct}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{tangentEquiv}.\mathrm{symm}(v),\mathrm{Matrix}.\mathrm{mulVec}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(s),\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{tangentEquiv}.\mathrm{symm}(v)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintFiniteMaximum.finite_sign_maximum_tangent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse of tangentEquiv supplies the coordinates of every tangent vector.

**Theorem 1.10 (Both directions of negative definiteness).**

$$(\forall v:\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{tangent},v\neq0\implies\mathrm{secondVariation}((v:\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{State}))<0)\iff(\forall s:\mathrm{Fin} 32,\mathrm{Matrix}.\mathrm{PosDef}(-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(s)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintFiniteMaximum.negativity_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Necessity bounds each branch by the strictly negative maximum. Sufficiency uses the finite-maximum strict inequality criterion. Symmetry is proved independently of the LDL certificates. The integer attainability clause is also checked below; it is not needed to infer either direction from the exact maximum identity.

**Theorem 1.11 (Strict negativity for this ququint state).**

$$\forall v:\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{tangent},v\neq0\implies\mathrm{secondVariation}((v:\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{State}))<0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintFiniteMaximum.second_variation_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The implication from the criterion consumes all_branches_negative, so all thirty-two LDL conclusions are on the live proof path to strict negativity.

**Theorem 1.12 (The explicit integer witnesses have all required signs).**

$$\forall s:\mathrm{Fin} 32,\forall i:\mathrm{Fin} 5,0<\mathrm{signValue}(s,i)\cdot\mathrm{dotProduct}(((j:\mathrm{Fin} 4)\mapsto(\mathrm{integerWitness}(s,j):\mathbb{R})),\mathrm{Matrix}.\mathrm{mulVec}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{zeroQ}(i),((j:\mathrm{Fin} 4)\mapsto(\mathrm{integerWitness}(s,j):\mathbb{R}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintFiniteMaximum.integerWitness_signs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

integerWitness is the explicit thirty-two-case integer table in Lean. All 160 strict sign inequalities follow from rational bounds for the positive radical and its square and cube; no floating-point result is trusted.

**Theorem 1.13 (Every sign pattern is attained with integer coordinates).**

$$\forall s:\mathrm{Fin} 32,\exists a:(\mathrm{Fin} 4\to\mathbb{R}),(\forall j:\mathrm{Fin} 4,\exists n:\mathbb{Z},a(j)=(n:\mathbb{R})) \land a\neq0 \land (\forall i:\mathrm{Fin} 5,0<\mathrm{signValue}(s,i)\cdot\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{wigner}((\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{tangentEquiv}(a):\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{State}),(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateBridge}.\mathrm{zeroIndex}(i)).1,(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateBridge}.\mathrm{zeroIndex}(i)).2))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintFiniteMaximum.sign_patterns_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same witnesses are nonzero and lie in the actual tangent subspace through tangentEquiv. Positive signValue times Wigner value certifies the requested strict sign.

QuquintStrictDecrease consumes the negative second variation to prove the normalized exact change and strict decrease of lOne and log lOne. This result concerns only the specified ququint state and constrained tangent family; it makes no claim about other dimensions, other critical points, general mana extremisation, author-verbatim Claim C, or global novelty.

## References

- Truth anchor: `D5/S3/Quantum/Magic/QuquintFiniteMaximum.branchMaximum`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintFiniteMaximum.branch_eval`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintFiniteMaximum.finite_sign_maximum`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintFiniteMaximum.finite_sign_maximum_tangent`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintFiniteMaximum.integerWitness`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintFiniteMaximum.integerWitness_signs`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintFiniteMaximum.negativity_iff`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintFiniteMaximum.secondVariation`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintFiniteMaximum.secondVariation_coordinates`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintFiniteMaximum.second_variation_negative`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintFiniteMaximum.signPattern`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintFiniteMaximum.signValue`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintFiniteMaximum.sign_patterns_attained`
- Dependency: [D5/S3/Quantum/Magic/QuquintCertificateAssembly](QuquintCertificateAssembly.md)
- Dependency: [D5/S3/Quantum/Magic/QuquintCertificateBridge](QuquintCertificateBridge.md)
