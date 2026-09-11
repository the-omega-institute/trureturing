# Weil Archimedean Tail Jet

## Abstract

A boundary-moment jet controls every even coefficient direction of the canonical arithmetic Gamma tail at every order and past-band frequency.

N and m are natural numbers. L is the support length, rho=2*pi/L, and v is an arbitrary complex vector indexed by 0,...,N with ordinary Euclidean mass sum_k |v_k|^2. The weights sigma_0=1 and sigma_k=sqrt(2) for k>0 implement the isometric even embedding. Set x_k=(rho*k/t)^2, q=(rho*N/t)^2, R=sum_k sigma_k*v_k/(1-x_k), P=sum_k sigma_k*v_k*sum_{j<m} x_k^j, and w=(2*rho/pi^2)*Zeta23.EF.gammaBracket(t)*sin(L*t/2)^2/t^2. The compatible physical cosine basis on [-L/2,L/2] has diagonal phase (-1)^k. This phase is part of the convention, not an omitted sign.

**Definition 1.1 (The exact canonical Cauchy density).**

$$\operatorname{D}(L, t, v)= \operatorname{w}(L, t) {\operatorname{norm}(\operatorname{R}(L, t, v))}^{2}$$

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilArchimedeanTailJet.evenArchimedeanTailDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The density retains the existing gammaBracket exactly. Its identification with the trigonometric Galerkin tail is the Cauchy-density calculation of Groskin, arXiv:2607.02828, Theorem 3.2; the Fourier-to-density identification is a cited analytic input and is not asserted as a Lean theorem here.

**Definition 1.2 (Retain the finite boundary-moment jet).**

$$\operatorname{J}(m, L, t, v)= \operatorname{w}(L, t) {\operatorname{norm}(\operatorname{P}(m, L, t, v))}^{2}$$

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilArchimedeanTailJet.evenArchimedeanJetDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite jet is a sum of the even boundary moments of orders 0,2,...,2*(m-1). No moment is set to zero. The prime and pole pieces of the complete Weil form are not redefined. The order-zero jet is the empty sum and is included.

**Theorem 1.3 (An all-direction, all-order density error bound).**

$$\operatorname{Positive}(L)\land \operatorname{Positive}(t-rho N) \Rightarrow \operatorname{abs}(\operatorname{D}(L, t, v)-\operatorname{J}(m, L, t, v))\leq \operatorname{abs}(\operatorname{w}(L, t)) 2 {q}^{m} {\operatorname{inv}(1-q)}^{2} {2 N+1} \operatorname{EuclideanMass}(v)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilArchimedeanTailJet.even_archimedean_tail_density_jet_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive(x) means 0<x. The assumptions are exactly L>0 and rho*N<t; they imply 0<=q<1 and include N=0. The conclusion holds for every complex coefficient vector. The proof uses the exact finite geometric remainder, two norm bounds, and sum sigma_k^2=2*N+1 through finite Cauchy-Schwarz. The sign of gammaBracket is not assumed. Even when both densities are positive, their difference need not be positive. Integration, the independent Gamma envelope, and the optimized positive projection correction are separate analytic results in the theory note, not conclusions of this Lean declaration. No complete-window complement gap, ground-state simplicity, or convergence of ground modes to Xi is asserted.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArchimedeanTailJet.evenArchimedeanJetDensity`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArchimedeanTailJet.evenArchimedeanTailDensity`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArchimedeanTailJet.even_archimedean_tail_density_jet_error`
