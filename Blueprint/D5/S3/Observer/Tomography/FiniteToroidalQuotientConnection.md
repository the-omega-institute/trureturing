# Finite Toroidal Quotient Connection

## Abstract

A finite positive toroidal Gram frame recovers its common two-point factor by a local kernel quotient.

**Theorem 1.1 (Finite toroidal Gram quotients recover the common factor).**

$$\forall Index \in \operatorname{Type}\left(\right), K \in \operatorname{Set}\left(\operatorname{Complex}\left(\right)\right), I \in \operatorname{Finset}\left(Index\right), w \in Index \to \operatorname{Real}\left(\right), P \in Index \to \left(\operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right)\right), T \in Index \to \left(\operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right)\right), xi \in \operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right),\; \left(\left(\forall j \in Index,\; \operatorname{mem}\left(j, I\right) \Rightarrow 0 < w\left(j\right)\right) \land \left(\left(\forall j \in Index, u \in \operatorname{Complex}\left(\right),\; \operatorname{mem}\left(j, I\right) \Rightarrow P\left(j\right)\left(u\right) = xi\left(u\right) \times T\left(j\right)\left(u\right)\right) \land \left(\forall u \in \operatorname{Complex}\left(\right),\; \operatorname{mem}\left(u, K\right) \Rightarrow \left(\exists j \in Index,\; \operatorname{mem}\left(j, I\right) \land T\left(j\right)\left(u\right) \ne 0\right)\right)\right)\right) \Rightarrow \left(\left(\forall u \in \operatorname{Complex}\left(\right),\; \operatorname{mem}\left(u, K\right) \Rightarrow \operatorname{weightedGramKernel}\left(I, w, T, u, u\right) \ne 0\right) \land \left(\forall s \in \operatorname{Complex}\left(\right), t \in \operatorname{Complex}\left(\right),\; \operatorname{weightedGramKernel}\left(I, w, T, s, t\right) \ne 0 \Rightarrow \operatorname{localQuotientKernel}\left(I, w, P, T, s, t\right) = xi\left(s\right) \times \operatorname{conj}\left(xi\left(t\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Tomography/FiniteToroidalQuotientConnection.finite_toroidal_frame_quotient_connection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The toric periods, twists, common factor, finite selection, and spectral window are explicit parameters. This isolates the algebraic content from external analytic constructions.

Strictly positive real weights and a nonzero selected twist at each window point make the carrier Gram kernel nonzero on the diagonal.

Pointwise period factorization pulls the common factor through the finite sum. At every pair where the carrier kernel is nonzero, division then gives the displayed quotient connection.

## References

- Truth anchor: `D5/S3/Observer/Tomography/FiniteToroidalQuotientConnection.finite_toroidal_frame_quotient_connection`
