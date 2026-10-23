# Real Readouts and Complete Positivity

## Abstract

On a finite complex matrix algebra, transpose symmetrization is the complex-linear map X to one half of X plus its transpose. It is positive and preserves trace. On Hermitian inputs its entries are the real parts of the input entries. Every symmetric trace readout is preserved.

**Theorem 1.1 (Real Readouts and Complete Positivity).**

$$\forall n:Type,[\operatorname{Fintype}(n)][\operatorname{DecidableEq}(n)],\forall a,b:n,a\neq b\Rightarrow \operatorname{Positive}(\operatorname{symmetrize}(n))\land \operatorname{TracePreserving}(\operatorname{symmetrize}(n))\land (\forall X:\operatorname{ComplexMatrix}(n),\operatorname{Hermitian}(X)\Rightarrow \forall i,j:n,\operatorname{entry}(\operatorname{symmetrize}(X),i,j)=\operatorname{Re}(\operatorname{X}(i,j)))\land \\(\forall E,X:\operatorname{ComplexMatrix}(n),\operatorname{transpose}(E)=E\Rightarrow \operatorname{Tr}(E\operatorname{symmetrize}(X))=\operatorname{Tr}(EX))\land \\\operatorname{Choi}(\operatorname{symmetrize}(n))\operatorname{antisymmetric}(a,b)=-\frac{1}{2}\operatorname{antisymmetric}(a,b)\land \frac{\operatorname{Choi}(\operatorname{symmetrize}(n))}{\operatorname{card}(n)}\operatorname{antisymmetric}(a,b)=-\frac{1}{2\operatorname{card}(n)}\operatorname{antisymmetric}(a,b)\land \neg \operatorname{CP}(\operatorname{symmetrize}(n))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/RealPartPositiveObstruction.real_part_readout_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a finite complex matrix algebra, transpose symmetrization is the complex-linear map X to one half of X plus its transpose. It is positive and preserves trace. On Hermitian inputs its entries are the real parts of the input entries. Every symmetric trace readout is preserved.

For two distinct basis indices a and b, the antisymmetric tensor e_a tensor e_b minus e_b tensor e_a is an eigenvector of the actual unnormalized Choi matrix with eigenvalue minus one half. Its quadratic value is minus one, so the Choi matrix is not positive semidefinite. The finite Kraus and Choi equivalence therefore excludes complete positivity.

The normalized Choi eigenvalue in dimension d is minus one over two d. Statistical preservation by a positive map does not supply a quantum channel valid on arbitrary ancillary extensions. Measurement-relative compression is studied by Bluhm, Rauber and Wolf, arXiv:1708.04898v4; Koashi and Imoto, quant-ph/0101144, provide broader no-disturbance structure. No novelty or optimality claim is made.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/RealPartPositiveObstruction.real_part_readout_obstruction`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../Foundation/FiniteKrausRepresentation.md)
