# Finite-Mode Positive Williamson Form

## Abstract

Oriented skew paired-plane induction constructs one positive Williamson congruence for any finite set of modes, including the empty set.

**Theorem 1.1 (An actual oriented paired orthonormal frame).**

$$\forall E, a, \operatorname{FiniteRealInnerProductSpace}\left(E\right) \land \operatorname{Even}\left(\operatorname{finrank}\left(E\right)\right) \land \operatorname{Skew}\left(a\right) \Rightarrow \exists K, b, nu, \operatorname{Finite}\left(K\right) \land \operatorname{OrthonormalBasis}\left(\operatorname{Sum}\left(K, K\right), b\right) \land \operatorname{Nonnegative}\left(nu\right) \land \operatorname{PairedAction}\left(a, b, nu\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/PositiveDefiniteWilliamson.skew_paired_basis_induction` (`✓ std3`). ∎

*Citation.* PK (2026). *The Williamson normal form in QIQT-H*. URL: <https://github.com/kaplan196883/QIQT-H/blob/0313e288c7ab3d3868c73ccdc6a68242efc0214a/lean/mathlib/QIQTH/WilliamsonNormalForm.lean>.

*Commentary.*

For every even-dimensional finite real inner product space E and every real linear skew operator a, there are a finite index set K, a complete orthonormal basis indexed by K plus K, and nonnegative frequencies nu. The action is a(p_k)=-nu_k q_k and a(q_k)=nu_k p_k. Zero dimension and the zero operator are included.

The construction extracts an invariant orthonormal plane from a negative Rayleigh eigenvalue of a squared, or an arbitrary orthonormal pair when a is zero. Skew adjointness makes the plane's orthogonal complement invariant. Strong induction and orthonormal gluing produce the whole frame, without assuming a paired-basis certificate.

**Theorem 1.2 (The same symplectic matrix supplies the energy congruence).**

$$\forall L, M, \operatorname{Finite}\left(L\right) \land \operatorname{PosDef}\left(M\right) \Rightarrow \exists S, nu, \operatorname{Symplectic}\left(S\right) \land \operatorname{Positive}\left(nu\right) \land \operatorname{transpose}\left(S\right) \cdot J \cdot S = J \land \operatorname{transpose}\left(S\right) \cdot M \cdot S = \operatorname{diag}\left(nu, nu\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/PositiveDefiniteWilliamson.positive_definite_williamson` (`✓ std3`). ∎

*Citation.* PK (2026). *The Williamson normal form in QIQT-H*. URL: <https://github.com/kaplan196883/QIQT-H/blob/0313e288c7ab3d3868c73ccdc6a68242efc0214a/lean/mathlib/QIQTH/WilliamsonNormalForm.lean>.

*Commentary.*

For any finite mode set L and real positive-definite matrix M on L plus L, one actual matrix S is symplectic and satisfies S-transpose J S=J and S-transpose M S=diag(nu,nu), with every frequency strictly positive. The theorem has no nonempty-mode hypothesis.

Set R=sqrt(M) and apply the paired-frame induction to A=R J R. The resulting orthogonal O puts A into the block form with upper-right diag(nu) and lower-left -diag(nu). Invertibility of A and nonzero basis vectors force positive frequencies. With E=[[0,sqrt(D)],[sqrt(D),0]], the single S=R-inverse O E gives both symplectic relations and the repeated diagonal energy.

This is an attributed port of PK's selected QIQT-H source. Mathlib supplies the Rayleigh, adjoint-complement, basis, coordinate, functional-calculus and matrix inverse interfaces.

Mathlib J=[[0,-I],[I,0]] is the negative of physical J+. The same S preserves both signs. The result supplies only a supporting matrix step for original theorem 2.4 within consolidated theorem 2.3; the observation-compatible split, metaplectic implementation, domains, completed tensor factorization and Gibbs trace identities require separate results.

## References

- Truth anchor: `D5/S3/QuadraticForms/PositiveDefiniteWilliamson.positive_definite_williamson`
- Truth anchor: `D5/S3/QuadraticForms/PositiveDefiniteWilliamson.skew_paired_basis_induction`
