# Finite Record Cosine Obstruction

## Abstract

A strictly positive cosine error floor for every recovery of the finite-record channel.

**Theorem 1.1 (Signed coefficient bound).**

$$\forall N \in \mathbb{N}, c \in \mathbb{Z} \to \mathbb{C},\; \left(\left(\forall k \in \mathbb{Z},\; \left(k < 0 \lor \operatorname{int}\left(N\right) < k\right) \Rightarrow c\left(k\right) = 0\right) \land \sum_{k \in \mathbb{Z}} {\operatorname{norm}\left(c\left(k\right)\right)^{2}} = 1\right) \Rightarrow \left(\forall ell \in \mathbb{Z},\; ell \ne 0 \Rightarrow \operatorname{norm}\left(\sum_{k \in \mathbb{Z}} {c\left(k + ell\right) \cdot \operatorname{conj}\left(c\left(k\right)\right)}\right) \le \operatorname{cos}\left(\frac{pi}{\operatorname{real}\left(\operatorname{natDiv}\left(N, \operatorname{natAbs}\left(ell\right)\right)\right) + 2}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FiniteRecordCosineObstruction.coefficient_gamma_le_cosine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The norms of coefficients in each residue class form a zero-padded finite path. Reindexing preserves the entire squared-norm mass, and the triangle inequality bounds the complex autocorrelation by the adjacent products. The squared zero-boundary averaging estimate and finite Cauchy-Schwarz bound each path. Conjugation transports the result to negative gaps.

**Theorem 1.2 (Positive recovery obstruction).**

$$\forall iota \in Type, fintype \in \operatorname{Fintype}\left(iota\right), decidableEq \in \operatorname{DecidableEq}\left(iota\right), N \in \mathbb{N}, c \in \mathbb{Z} \to \mathbb{C}, q \in iota \to \mathbb{Z},\; \left(\left(\forall k \in \mathbb{Z},\; \left(k < 0 \lor \operatorname{int}\left(N\right) < k\right) \Rightarrow c\left(k\right) = 0\right) \land \sum_{k \in \mathbb{Z}} {\operatorname{norm}\left(c\left(k\right)\right)^{2}} = 1\right) \Rightarrow \operatorname{let} \forall t \in \mathbb{Z},\; gamma\left(t\right) = \sum_{k \in \mathbb{Z}} {c\left(k + t\right) \cdot \operatorname{conj}\left(c\left(k\right)\right)}; \operatorname{let} Q = \sum_{i \in iota} {\operatorname{natAbs}\left(q\left(i\right)\right)}; \operatorname{let} L = N + 2 \cdot Q + 1; \operatorname{let} \forall a \in \operatorname{Fin}\left(L\right),\; coord\left(a\right) = \operatorname{int}\left(\operatorname{val}\left(a\right)\right) - \operatorname{int}\left(Q\right); \operatorname{let} \forall i \in iota, a \in \operatorname{Fin}\left(L\right),\; record\left(i, a\right) = c\left(coord\left(a\right) + q\left(i\right)\right); \operatorname{let} \forall p \in \operatorname{Product}\left(iota, \operatorname{Fin}\left(L\right)\right), j \in iota,\; V\left(p, j\right) = \operatorname{ite}\left(j = \operatorname{fst}\left(p\right), record\left(\operatorname{fst}\left(p\right), \operatorname{snd}\left(p\right)\right), 0\right); \operatorname{let} \forall joint \in \operatorname{Matrix}\left(\operatorname{Product}\left(iota, \operatorname{Fin}\left(L\right)\right), \operatorname{Product}\left(iota, \operatorname{Fin}\left(L\right)\right), \mathbb{C}\right), i \in iota, j \in iota,\; partialTrace\left(joint\right)\left(i, j\right) = \sum_{a \in \operatorname{Fin}\left(L\right)} {joint\left(\operatorname{pair}\left(i, a\right), \operatorname{pair}\left(j, a\right)\right)}; \operatorname{let} \forall A \in \operatorname{Matrix}\left(iota, iota, \mathbb{C}\right),\; Lambda\left(A\right) = partialTrace\left(V \cdot A \cdot \operatorname{conjTranspose}\left(V\right)\right); \exists C \in \operatorname{QuantumChannel}\left(iota, iota\right),\; \left(\left(\forall A \in \operatorname{Matrix}\left(iota, iota, \mathbb{C}\right),\; \operatorname{act}\left(C, A\right) = Lambda\left(A\right)\right) \land \left(\forall A \in \operatorname{Matrix}\left(iota, iota, \mathbb{C}\right), i \in iota, j \in iota,\; Lambda\left(A\right)\left(i, j\right) = gamma\left(q\left(i\right) - q\left(j\right)\right) \cdot A\left(i, j\right)\right)\right) \land \left(\forall i \in iota, j \in iota, ell \in \mathbb{Z},\; ell \ne 0 \Rightarrow \left(q\left(i\right) - q\left(j\right) = ell \Rightarrow \left(\forall R \in \operatorname{QuantumChannel}\left(iota, iota\right),\; \operatorname{let} f = \operatorname{IntFloor}\left(\frac{\operatorname{real}\left(N\right)}{\operatorname{abs}\left(\operatorname{real}\left(ell\right)\right)}\right); \operatorname{let} bound = \frac{1 - \operatorname{cos}\left(\frac{pi}{\operatorname{real}\left(f\right) + 2}\right)}{2}; \operatorname{let} errors = \operatorname{range}\left({rho \in \operatorname{DensityState}\left(iota\right)} \mapsto \operatorname{traceDistance}\left(\operatorname{mapState}\left(R, \operatorname{mapState}\left(C, rho\right)\right), rho\right)\right); \operatorname{let} matrixErrors = \operatorname{range}\left({rho \in \operatorname{DensityState}\left(iota\right)} \mapsto \frac{\operatorname{traceNorm}\left(\operatorname{act}\left(R, Lambda\left(\operatorname{raw}\left(rho\right)\right)\right) - \operatorname{raw}\left(rho\right)\right)}{2}\right); \left(\left(\left(\left(errors = matrixErrors \land \left(\forall rho \in \operatorname{DensityState}\left(iota\right), sigma \in \operatorname{DensityState}\left(iota\right),\; 0 \le \operatorname{traceDistance}\left(rho, sigma\right) \land \operatorname{traceDistance}\left(rho, sigma\right) \le 1\right)\right) \land \operatorname{Nonempty}\left(errors\right)\right) \land \operatorname{BddAbove}\left(errors\right)\right) \land bound \le \operatorname{sSup}\left(errors\right)\right) \land 0 < bound\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FiniteRecordCosineObstruction.finite_record_cosine_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The recording matrix followed by the displayed partial trace realizes one canonical CPTP channel with the stated action on every complex matrix. The all-density recovery lower bound in terms of the norm of gamma combines with the signed coefficient estimate. Natural division equals the natural floor of the nonnegative real quotient, whose integer floor is its integer cast. The angle is strictly positive and at most pi over two, so this same cosine margin is strictly positive.

The coefficients are complex and may have arbitrary phases and internal zeros. N may be zero, the selected gap may have either sign or exceed N in absolute value, and all other labels may repeat. The type iota has an arbitrary universe, a Fintype instance, and decidable equality.

Every sum over the integers denotes the literal Lean tsum. natDiv denotes division in Nat; the fraction inside IntFloor is division in Real. real and int denote the displayed scalar casts, and natAbs is integer absolute value valued in Nat. The nonzero gap gives a nonzero absolute-value denominator; its floor plus two is positive and nonzero.

QuantumChannel and DensityState are the canonical CPTP maps and all density matrices from FiniteStateChannel. raw applies CStarMatrix.ofMatrix.symm to the density state's value. act is the canonical map in matrix coordinates. traceNorm is the real trace of the positive square root of the matrix Gram matrix, and traceDistance is one half of that trace norm on the difference. The supremum is the real sSup of the displayed range over all density states.

This obstruction is specific to the displayed finite-record channel and a realized nonzero label gap. Unaffected degenerate subspaces remain outside its obstruction claim. It does not assert an obstruction for arbitrary encodings or physical realizations, nor a Hamiltonian, energy, locality, cost, or recovery-algorithm statement. Cosine-bound attainment and the adjacent uniform-coefficient example are separate statements.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/FiniteRecordCosineObstruction.coefficient_gamma_le_cosine`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FiniteRecordCosineObstruction.finite_record_cosine_obstruction`
- Dependency: [D5/S3/Quantum/Decoherence/FiniteRecordRecoveryError](../Decoherence/FiniteRecordRecoveryError.md)
- Dependency: [D5/S3/QuantumBounds/ReferenceFrameTaxOptimal](../../QuantumBounds/ReferenceFrameTaxOptimal.md)
