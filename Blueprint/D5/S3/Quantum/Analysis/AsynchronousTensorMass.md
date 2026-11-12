# The full algebraic tensor fixed dual

## Abstract

The asynchronous algebraic tensor sum has only the original tensor mass as fixed functional.

This is the original arbitrary finite asynchronous tensor carrier of Quantum Origin V, Lemma 79.3. Finite I with positive weights summing to one is necessarily nonempty, so it includes every r at least one without restricting r. The normalized set is the entire CircuitBalancedConfirmation.base of C.toPointedCone and the original u, with compactness, convexity and spanning given by the same normalized base geometry. All dual functionals are real algebraic functionals. The tensor product is used only for its universal property and its pure-tensor spanning property. The full complex spectral disk, peripheral semisimplicity and algebraic multiplicity-one assertions remain separate obligations.

**Definition 1.1 (The algebraic asynchronous sum).**

$$\forall vA \in \operatorname{Universe}\left(\right),\; \forall A \in \operatorname{Type}\left(vA\right),\; [\operatorname{NormedAddCommGroup}\left(A\right)] [\operatorname{NormedSpace}\left(\operatorname{Real}\left(\right), A\right)] \forall vI \in \operatorname{Universe}\left(\right),\; \forall I \in \operatorname{Type}\left(vI\right),\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall Phi \in \operatorname{LinearMap}\left(\operatorname{Real}\left(\right), A, A\right),\; \forall alpha \in I \to \operatorname{Real}\left(\right),\; \operatorname{asynchronous}\left(Phi, alpha\right) = \operatorname{sum}\left({j:I}\mapsto \operatorname{smul}\left(alpha\left(j\right), \operatorname{tensorMap}\left({i:I}\mapsto \operatorname{ifThenElse}\left(i = j, Phi, \operatorname{identity}\left(A\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Analysis/AsynchronousTensorMass.asynchronous` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier is the actual finite algebraic real PiTensorProduct. The sum updates one slot by Phi and leaves every other slot unchanged. Alpha may be arbitrary in this definition; the theorem imposes strict positivity and total mass one. No positive cone on this tensor product and no physical copies are supplied.

**Definition 1.2 (The original tensor mass functional).**

$$\forall vA \in \operatorname{Universe}\left(\right),\; \forall A \in \operatorname{Type}\left(vA\right),\; [\operatorname{NormedAddCommGroup}\left(A\right)] [\operatorname{NormedSpace}\left(\operatorname{Real}\left(\right), A\right)] \forall vI \in \operatorname{Universe}\left(\right),\; \forall I \in \operatorname{Type}\left(vI\right),\; [\operatorname{Fintype}\left(I\right)] \forall u \in \operatorname{Dual}\left(\operatorname{Real}\left(\right), A\right),\; \forall a \in I \to A,\; \operatorname{tensorMass}\left(u\right)\left(\operatorname{tprod}\left(\operatorname{Real}\left(\right), a\right)\right) = \operatorname{prod}\left({i:I}\mapsto u\left(a\left(i\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Analysis/AsynchronousTensorMass.tensorMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The universal-property lift of the multilinear product of the original u is the tensor mass. Its value on each pure tensor is the product of the original slot masses.

**Theorem 1.3 (The action on every pure tensor).**

$$\forall vA \in \operatorname{Universe}\left(\right),\; \forall A \in \operatorname{Type}\left(vA\right),\; [\operatorname{NormedAddCommGroup}\left(A\right)] [\operatorname{NormedSpace}\left(\operatorname{Real}\left(\right), A\right)] \forall vI \in \operatorname{Universe}\left(\right),\; \forall I \in \operatorname{Type}\left(vI\right),\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall Phi \in \operatorname{LinearMap}\left(\operatorname{Real}\left(\right), A, A\right),\; \forall alpha \in I \to \operatorname{Real}\left(\right),\; \forall a \in I \to A,\; \operatorname{asynchronous}\left(Phi, alpha\right)\left(\operatorname{tprod}\left(\operatorname{Real}\left(\right), a\right)\right) = \operatorname{sum}\left({j:I}\mapsto \operatorname{smul}\left(alpha\left(j\right), \operatorname{tprod}\left(\operatorname{Real}\left(\right), \operatorname{update}\left(a, j, Phi\left(a\left(j\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/AsynchronousTensorMass.asynchronous_tprod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply PiTensorProduct.map_tprod to each slot map and distribute the finite linear sum. This formula is the step used to pass between a fixed tensor functional and its multilinear form.

The classical flip qualification in Corollary 79.4 follows directly from this action formula. Let v be any nonzero real vector with Phi(v)=-v and let the finite weights sum to one. Multilinearity gives tprod(update(const(v),j,-v))=-tprod(const(v)) for every slot j. The weighted sum is therefore -tprod(const(v)). This is an eigenvalue -1 for every positive tensor order. To check that the tensor is nonzero, choose a real dual f with f(v)=1, using Module.Projective.exists_dual_eq_one. Applying tensorMass(f) to tprod(const(v)) gives the product of ones, hence one. If u(v)=0 and the index type is nonempty, tensorMass(u) evaluates to zero. For the classical two-state flip, v=(1,-1) is precisely such a zero-mass vector. Thus fixed-dual rigidity does not imply convergence of asynchronous iterates, loss of all correlations, a decay rate or a physical continuous time evolution. This is an algebraic consequence of the displayed action and the multilinear laws; it needs no cone on the tensor space.

$\forall vA \in \operatorname{Universe}\left(\right),\; \forall A \in \operatorname{Type}\left(vA\right),\; [\operatorname{NormedAddCommGroup}\left(A\right)] [\operatorname{NormedSpace}\left(\operatorname{Real}\left(\right), A\right)] \forall vI \in \operatorname{Universe}\left(\right),\; \forall I \in \operatorname{Type}\left(vI\right),\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall Phi \in \operatorname{LinearMap}\left(\operatorname{Real}\left(\right), A, A\right),\; \forall alpha \in I \to \operatorname{Real}\left(\right),\; \forall v \in A,\; \operatorname{sum}\left(alpha\right) = 1 \Rightarrow \left(v \neq 0 \Rightarrow \left(Phi\left(v\right) = 0 - v \Rightarrow \left(\operatorname{asynchronous}\left(Phi, alpha\right)\left(\operatorname{tprod}\left(\operatorname{Real}\left(\right), {i:I}\mapsto v\right)\right) = \operatorname{smul}\left(0 - 1, \operatorname{tprod}\left(\operatorname{Real}\left(\right), {i:I}\mapsto v\right)\right) \land \operatorname{tprod}\left(\operatorname{Real}\left(\right), {i:I}\mapsto v\right) \neq 0\right)\right)\right)$

**Theorem 1.4 (All real fixed functionals, with an exact converse).**

$$\forall vA \in \operatorname{Universe}\left(\right),\; \forall A \in \operatorname{Type}\left(vA\right),\; [\operatorname{NormedAddCommGroup}\left(A\right)] [\operatorname{NormedSpace}\left(\operatorname{Real}\left(\right), A\right)] [\operatorname{FiniteDimensional}\left(\operatorname{Real}\left(\right), A\right)] [\operatorname{Nontrivial}\left(A\right)] \forall vI \in \operatorname{Universe}\left(\right),\; \forall I \in \operatorname{Type}\left(vI\right),\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall C \in \operatorname{ProperCone}\left(\operatorname{Real}\left(\right), A\right),\; \forall u \in \operatorname{Dual}\left(\operatorname{Real}\left(\right), A\right),\; \forall Phi \in \operatorname{LinearMap}\left(\operatorname{Real}\left(\right), A, A\right),\; \forall alpha \in I \to \operatorname{Real}\left(\right),\; \forall g \in \operatorname{Dual}\left(\operatorname{Real}\left(\right), \operatorname{PiTensorProduct}\left(\operatorname{Real}\left(\right), \operatorname{constantFamily}\left(I, A\right)\right)\right),\; \operatorname{span}\left(\operatorname{Real}\left(\right), C\right) = \operatorname{top}\left(\operatorname{Submodule}\left(\operatorname{Real}\left(\right), A\right)\right) \Rightarrow \left(\left(\forall x \in A,\; \operatorname{Mem}\left(x, C\right) \Rightarrow \left(x \neq 0 \Rightarrow 0 < u\left(x\right)\right)\right) \Rightarrow \left(\operatorname{MapsTo}\left(Phi, C, C\right) \Rightarrow \left(\operatorname{comp}\left(u, Phi\right) = u \Rightarrow \left(\left(\forall f \in \operatorname{Dual}\left(\operatorname{Real}\left(\right), A\right),\; \operatorname{comp}\left(f, Phi\right) = f \Rightarrow \left(\exists c \in \operatorname{Real}\left(\right),\; f = \operatorname{smul}\left(c, u\right)\right)\right) \Rightarrow \left(\left(\forall i \in I,\; 0 < alpha\left(i\right)\right) \Rightarrow \left(\operatorname{sum}\left(alpha\right) = 1 \Rightarrow \left(\operatorname{comp}\left(g, \operatorname{asynchronous}\left(Phi, alpha\right)\right) = g \Leftrightarrow \left(\exists c \in \operatorname{Real}\left(\right),\; g = \operatorname{smul}\left(c, \operatorname{tensorMass}\left(u\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/AsynchronousTensorMass.fixed_tensor_dual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary nonzero finite-dimensional real proper-cone data and every finite positive weight family, a real linear functional on the full algebraic tensor carrier is fixed exactly when it is a scalar multiple of the original tensor mass. Evaluating on pure tensors gives the asynchronous multilinear identity; the proved maximum principle gives factorization, and the universal property gives equality on the whole tensor space. The converse uses u composed with Phi equals u and the sum of the weights. This establishes only the fixed-space clause of (79.6), not algebraic simplicity or the complex spectral clauses of Lemma 79.3.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/AsynchronousTensorMass.asynchronous`
- Truth anchor: `D5/S3/Quantum/Analysis/AsynchronousTensorMass.asynchronous_tprod`
- Truth anchor: `D5/S3/Quantum/Analysis/AsynchronousTensorMass.fixed_tensor_dual`
- Truth anchor: `D5/S3/Quantum/Analysis/AsynchronousTensorMass.tensorMass`
- Dependency: [D5/S3/Quantum/Analysis/AsynchronousMassRigidity](AsynchronousMassRigidity.md)
