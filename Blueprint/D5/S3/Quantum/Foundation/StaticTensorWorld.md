# A closed static world with nonassociative local comparison

## Abstract

A closed world of all finite real tensor words has positive Frobenius comparisons, every actual module and conditional-action identity, zero generators at every label, and a nonassociative symmetric-matrix local object.

The local space is the entire real symmetric two by two matrix space, with symmetrized matrix multiplication and the trace pairing. Every finite parenthesized tensor word, including the empty word, is supplied. Every ordered pair of words has an actual edge whose output is the same object later reused in the family. No active object or quantum representation is assumed.

**Definition 1.1 (Finite positive comparison objects).**

$$\forall (A: \operatorname{Comparison}), (\operatorname{NontrivialFiniteRealInnerProductSpace}(\operatorname{Carrier}(A))) \land (\operatorname{RealBilinear}(\operatorname{mul}(A))) \land (\operatorname{RealLinear}(\operatorname{action}(A))) \land (\forall (x: \operatorname{Carrier}(A)), \forall (y: \operatorname{Carrier}(A)), \operatorname{mul}(A, x, y) = \operatorname{mul}(A, y, x)) \land (\forall (x: \operatorname{Carrier}(A)), \operatorname{mul}(A, \operatorname{unit}(A), x) = x) \land (\forall (x: \operatorname{Carrier}(A)), \forall (y: \operatorname{Carrier}(A)), \forall (z: \operatorname{Carrier}(A)), \operatorname{InnerProduct}(A, \operatorname{mul}(A, x, y), z) = \operatorname{InnerProduct}(A, y, \operatorname{mul}(A, x, z))) \land (\forall (h: \operatorname{Carrier}(A)), \forall (x: \operatorname{Carrier}(A)), \forall (y: \operatorname{Carrier}(A)), \operatorname{action}(A, h, \operatorname{mul}(A, x, y)) = \operatorname{mul}(A, \operatorname{action}(A, h, x), y) + \operatorname{mul}(A, x, \operatorname{action}(A, h, y)))$$

*Formalization.* `D5/S3/Quantum/Foundation/StaticTensorWorld.Comparison` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Comparison bundles a nontrivial finite-dimensional real inner product space E, a unit e, a real bilinear operation S, and a real linear label assignment D into real linear endomorphisms. S is commutative, S(e,x)=x, the inner product satisfies the Frobenius identity, and D(h) is a derivation of this same S for every h. The inner product structure supplies symmetry, bilinearity and strict positivity on every nonzero vector. No Jordan, associative, alternating or Lie identity is included.

**Definition 1.2 (Zero assignment at every label).**

$$\forall (A: \operatorname{Comparison}), \operatorname{IsStatic}(A) \iff \operatorname{action}(A) = 0$$

*Formalization.* `D5/S3/Quantum/Foundation/StaticTensorWorld.IsStatic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An object is static exactly when its entire linear map into endomorphisms is zero. This quantifies every label and every vector. It is stronger than setting one chosen Hamiltonian to zero.

**Definition 1.3 (The full actual binary contract).**

$$\forall (A: \operatorname{Comparison}), \forall (B: \operatorname{Comparison}), \forall (C: \operatorname{Comparison}), \forall (e: \operatorname{ActualEdge}(A, B, C)), (\operatorname{RealLinearEquivalence}(\operatorname{carrier}(e), \operatorname{Carrier}(C), \operatorname{RealTensorProduct}(\operatorname{Carrier}(A), \operatorname{Carrier}(B)))) \land (\operatorname{carrier}(e, \operatorname{unit}(C)) = \operatorname{Tensor}(\operatorname{unit}(A), \operatorname{unit}(B))) \land (\forall (x: \operatorname{Carrier}(A)), \forall (y: \operatorname{Carrier}(B)), \forall (z: \operatorname{Carrier}(A)), \forall (t: \operatorname{Carrier}(B)), \operatorname{InnerProduct}(C, \operatorname{inverseCarrier}(e, \operatorname{Tensor}(x, y)), \operatorname{inverseCarrier}(e, \operatorname{Tensor}(z, t))) = \operatorname{InnerProduct}(A, x, z) \cdot \operatorname{InnerProduct}(B, y, t)) \land (\forall (x: \operatorname{Carrier}(A)), \forall (z: \operatorname{Carrier}(A)), \forall (t: \operatorname{Carrier}(B)), \operatorname{carrier}(e, \operatorname{mul}(C, \operatorname{inverseCarrier}(e, \operatorname{Tensor}(x, \operatorname{unit}(B))), \operatorname{inverseCarrier}(e, \operatorname{Tensor}(z, t)))) = \operatorname{Tensor}(\operatorname{mul}(A, x, z), t)) \land (\forall (y: \operatorname{Carrier}(B)), \forall (z: \operatorname{Carrier}(A)), \forall (t: \operatorname{Carrier}(B)), \operatorname{carrier}(e, \operatorname{mul}(C, \operatorname{inverseCarrier}(e, \operatorname{Tensor}(\operatorname{unit}(A), y)), \operatorname{inverseCarrier}(e, \operatorname{Tensor}(z, t)))) = \operatorname{Tensor}(z, \operatorname{mul}(B, y, t))) \land (\forall (x: \operatorname{Carrier}(A)), \forall (y: \operatorname{Carrier}(B)), \forall (z: \operatorname{Carrier}(A)), \operatorname{carrier}(e, \operatorname{action}(C, \operatorname{inverseCarrier}(e, \operatorname{Tensor}(x, y)), \operatorname{inverseCarrier}(e, \operatorname{Tensor}(z, \operatorname{unit}(B))))) = \operatorname{Tensor}(\operatorname{action}(A, x, z), y)) \land (\forall (x: \operatorname{Carrier}(A)), \forall (y: \operatorname{Carrier}(B)), \forall (t: \operatorname{Carrier}(B)), \operatorname{carrier}(e, \operatorname{action}(C, \operatorname{inverseCarrier}(e, \operatorname{Tensor}(x, y)), \operatorname{inverseCarrier}(e, \operatorname{Tensor}(\operatorname{unit}(A), t)))) = \operatorname{Tensor}(x, \operatorname{action}(B, y, t)))$$

*Formalization.* `D5/S3/Quantum/Foundation/StaticTensorWorld.ActualEdge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For A,B,C, an actual edge carries a real linear equivalence from the entire carrier of C onto the algebraic tensor product of the carriers of A and B. It identifies the unit and the product pairing on simple tensors. Both module identities and both value-preserving conditional-action identities hold for all displayed arguments. C is the actual output Comparison, so its same multiplication, inner product and complete derivation law are retained on reuse. Product pairings are a permitted particular case of the arbitrary positive Frobenius pairing allowed by the source contract.

**Definition 1.4 (Actual pure tensor comparison).**

$$\forall (A: \operatorname{Comparison}), \forall (B: \operatorname{Comparison}), \operatorname{tensor}(A, B) = \operatorname{ComparisonData}(\operatorname{RealTensorCarrier}(A, B), \operatorname{BilinearTensor}(\operatorname{mul}(A), \operatorname{mul}(B)), \operatorname{ProductInner}(A, B), \operatorname{TensorUnit}(A, B), 0)$$

*Formalization.* `D5/S3/Quantum/Foundation/StaticTensorWorld.tensor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary positive Comparison objects A and B, tensor A B has the full real algebraic tensor carrier, the tensor unit, the bilinear tensor product of the two comparisons, the standard positive tensor inner product, and zero label assignment. The tensor comparison is commutative, unital and Frobenius for all joint vectors, including sums of simple tensors. Tensor inner-product positivity is the upstream positive tensor construction; it is not a premise asserting positivity of an invented family. When A and B are static, the identity carrier equivalence proves all actual-edge identities.

**Definition 1.5 (The actual local domain).**

$$\operatorname{SymTwo} = \operatorname{HermitianMat}(\operatorname{Fin}(2), \operatorname{Real})$$

*Formalization.* `D5/S3/Quantum/Foundation/StaticTensorWorld.SymTwo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

HermitianMat over the real field is precisely the full symmetric matrix subspace: real conjugation is trivial, so the adjoint is transpose. It has all real entries allowed by symmetry, with no discrete or rational restriction. The imported HermitianMat inner product is the actual trace of the matrix product, and the finite-dimensional and positive-definite structures are reused.

**Definition 1.6 (Symmetrized matrix comparison).**

$$\forall (a: \operatorname{SymTwo}), \forall (b: \operatorname{SymTwo}), \operatorname{mat}(\operatorname{symMul}(a, b)) = \frac{1}{2} (\operatorname{mat}(a)\operatorname{mat}(b) + \operatorname{mat}(b)\operatorname{mat}(a))$$

*Formalization.* `D5/S3/Quantum/Foundation/StaticTensorWorld.symMul` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The multiplication is the self-adjoint part of ordinary matrix multiplication. On symmetric real inputs its matrix is exactly one half of ac+ca. Trace cyclicity proves the Frobenius identity; symmetry and the matrix identity give commutativity and the unit law.

**Definition 1.7 (The symmetric-matrix comparison with zero assignment).**

$$\operatorname{localObject} = \operatorname{ComparisonData}(\operatorname{SymTwo}, \operatorname{symMul}, \operatorname{TracePairing}, \operatorname{Identity}, 0)$$

*Formalization.* `D5/S3/Quantum/Foundation/StaticTensorWorld.localObject` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The local carrier is SymTwo, the comparison is symMul, the unit is the identity matrix, the pairing is Tr(ac), and D is identically zero. Each of these is actual constructed data. Every label endomorphism is a derivation because both sides of the derivation identity vanish.

**Definition 1.8 (The empty-word scalar comparison).**

$$\operatorname{scalarObject} = \operatorname{ComparisonData}(\operatorname{Real}, \operatorname{RealMultiplication}, \operatorname{RealPairing}, 1, 0)$$

*Formalization.* `D5/S3/Quantum/Foundation/StaticTensorWorld.scalarObject` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty word has carrier R, ordinary multiplication and inner product, unit one, and zero assignment. It is finite and nontrivial.

**Definition 1.9 (All finite tensor words).**

$$\operatorname{Word} = \operatorname{FreeBinaryWords}(\operatorname{empty}, \operatorname{local})$$

*Formalization.* `D5/S3/Quantum/Foundation/StaticTensorWorld.Word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Word has constructors empty, local and pair(u,v), with arbitrary recursively generated finite u and v. There is no maximum length, finite-depth cap or restriction to a fixed parenthesization. Empty represents the real tensor unit; local represents the symmetric matrix object.

**Definition 1.10 (One unchanged object for each word).**

$$\operatorname{object}(\operatorname{empty}) = \operatorname{scalarObject}, \operatorname{object}(\operatorname{local}) = \operatorname{localObject}, \forall (u: \operatorname{Word}), \forall (v: \operatorname{Word}), \operatorname{object}(\operatorname{pair}(u, v)) = \operatorname{tensor}(\operatorname{object}(u), \operatorname{object}(v))$$

*Formalization.* `D5/S3/Quantum/Foundation/StaticTensorWorld.object` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The recursion defines an actual object at each finite word. At a pair, its carrier is definitionally the full real tensor product of the two previous carriers. Its comparison and inner product are the pure tensors of those same previous data. The same recursion is applied at every depth.

**Definition 1.11 (Closed all-static actual worlds).**

$$\forall (W: \operatorname{StaticWorld}), (\forall (w: \operatorname{Word}), \operatorname{IsStatic}(\operatorname{field}(W, w))) \land (\forall (u: \operatorname{Word}), \forall (v: \operatorname{Word}), \operatorname{ActualEdge}(\operatorname{field}(W, u), \operatorname{field}(W, v), \operatorname{field}(W, \operatorname{pair}(u, v))))$$

*Formalization.* `D5/S3/Quantum/Foundation/StaticTensorWorld.StaticWorld` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A StaticWorld provides a Comparison at every word, proves that all their label assignments are zero, and supplies an ActualEdge for every ordered pair into that world's same pair word. The object contract includes finite dimension, nonzero real carrier, positive Frobenius comparison and the full derivation law. The edge contract includes the complete module and conditional-action laws, rather than just unit-embedding equalities.

**Definition 1.12 (The constructed all-finite static world).**

$$\operatorname{counterworld} = \operatorname{StaticWorldData}(\operatorname{object})$$

*Formalization.* `D5/S3/Quantum/Foundation/StaticTensorWorld.counterworld` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This world uses the actual recursive object family. Each edge uses the identity equivalence on the real tensor carrier. For simple inputs its comparison is S_A(a,c) tensor S_B(b,d); the two module identities follow from the units. Both conditional actions are zero at every label, and the complete joint derivation law is zero equals zero plus zero for arbitrary joint vectors. All intermediate outputs remain in this same family and retain their same data. Every member is static, so no member can be an active partner for any other member.

**Definition 1.13 (The consequence that fails without active partners).**

$$\operatorname{claim} = \forall (W: \operatorname{StaticWorld}), \forall (w: \operatorname{Word}), \forall (a: \operatorname{Carrier}(\operatorname{field}(W, w))), \forall (b: \operatorname{Carrier}(\operatorname{field}(W, w))), \forall (c: \operatorname{Carrier}(\operatorname{field}(W, w))), \operatorname{mul}(\operatorname{field}(W, w), \operatorname{mul}(\operatorname{field}(W, w), a, b), c) = \operatorname{mul}(\operatorname{field}(W, w), a, \operatorname{mul}(\operatorname{field}(W, w), b, c))$$

*Formalization.* `D5/S3/Quantum/Foundation/StaticTensorWorld.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The claim says every comparison in every closed all-static actual world is associative. This is the static classical conclusion that the activity hypothesis would enforce; it is not a claim that a particular Hamiltonian must be nonzero. Refuting it requires the complete constructed world, not only a matrix identity detached from its joint contracts.

**Definition 1.14 (A real diagonal Pauli matrix).**

$$\operatorname{pauliZ} = \operatorname{Diagonal}(1, -1)$$

*Formalization.* `D5/S3/Quantum/Foundation/StaticTensorWorld.pauliZ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

pauliZ is diag(1,-1), as an element of the actual symmetric matrix space.

**Definition 1.15 (A real off-diagonal Pauli matrix).**

$$\operatorname{pauliX} = \operatorname{MatrixRows}(0, 1, 1, 0)$$

*Formalization.* `D5/S3/Quantum/Foundation/StaticTensorWorld.pauliX` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

pauliX has rows (0,1) and (1,0). In the actual local comparison, S(Z,X)=0 and S(X,X)=I. Hence S(S(Z,X),X)=0, while S(Z,S(X,X))=Z is nonzero. Equivalently the local left-multiplication commutator [L_Z,L_X]X is Z.

**Theorem 1.16 (Full static tensor closure does not force associativity).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/StaticTensorWorld.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the claimed universal associativity to counterworld, its local word and the actual matrices Z,X,X. The two nested products have unequal top-left entries, contradicting that claim. The counterworld already supplies all finite real domains, positive pairings and actual edges, and every generator at every label vanishes. Thus removing active partners leaves a complete static world with nonassociative local comparison. Nonassociativity also prevents this static local object from being a finite real direct-product classical algebra. This conclusion does not assert that the symmetric local comparison fails the Jordan identity, nor does it identify zero label assignment with the zero-Hamiltonian case of an otherwise active complex quantum object.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/StaticTensorWorld.ActualEdge`
- Truth anchor: `D5/S3/Quantum/Foundation/StaticTensorWorld.Comparison`
- Truth anchor: `D5/S3/Quantum/Foundation/StaticTensorWorld.IsStatic`
- Truth anchor: `D5/S3/Quantum/Foundation/StaticTensorWorld.StaticWorld`
- Truth anchor: `D5/S3/Quantum/Foundation/StaticTensorWorld.SymTwo`
- Truth anchor: `D5/S3/Quantum/Foundation/StaticTensorWorld.Word`
- Truth anchor: `D5/S3/Quantum/Foundation/StaticTensorWorld.claim`
- Truth anchor: `D5/S3/Quantum/Foundation/StaticTensorWorld.counterworld`
- Truth anchor: `D5/S3/Quantum/Foundation/StaticTensorWorld.localObject`
- Truth anchor: `D5/S3/Quantum/Foundation/StaticTensorWorld.object`
- Truth anchor: `D5/S3/Quantum/Foundation/StaticTensorWorld.pauliX`
- Truth anchor: `D5/S3/Quantum/Foundation/StaticTensorWorld.pauliZ`
- Truth anchor: `D5/S3/Quantum/Foundation/StaticTensorWorld.result`
- Truth anchor: `D5/S3/Quantum/Foundation/StaticTensorWorld.scalarObject`
- Truth anchor: `D5/S3/Quantum/Foundation/StaticTensorWorld.symMul`
- Truth anchor: `D5/S3/Quantum/Foundation/StaticTensorWorld.tensor`
