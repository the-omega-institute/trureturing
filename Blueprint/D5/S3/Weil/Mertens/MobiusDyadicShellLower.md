# The endpoint lower bound for signed Möbius shell energy

## Abstract

Each nontrivial zeta zero with real part at least one half forces arbitrarily late signed Möbius shells at its exact energy scale.

**Theorem 1.1 (Arbitrarily late shells at the zero exponent).**

$$\forall \rho \in \mathbb{C}, (\zeta\left(\rho\right)=0 \land 0 < \Re\left(\rho\right) < 1 \land \frac{1}{2} \leq \Re\left(\rho\right)) \implies \exists c \in \mathbb{R}, (0<c \land (\forall M \in \mathbb{N}, \exists k \in \mathbb{N}, M \leq k \land c (2^{2\Re\left(\rho\right) - 1})^{k} \leq E\left(k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/MobiusDyadicShellLower.exists_mobiusDyadicShellEnergy_ge_of_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write A(x) for the real sum of μ(n)/n over the positive integers n ≤ ⌊x⌋₊, where ⌊x⌋₊ is the natural floor. The signed difference is A(x) − A(2x). The shell energy E(k) is the Lebesgue integral of its square on (2^k, 2^(k+1)] with respect to unweighted dx.

For every complex ρ with ζ(ρ) = 0, 0 < Re(ρ) < 1, and 1/2 ≤ Re(ρ), there exists a real c > 0 such that for every natural M there exists a natural k ≥ M with E(k) ≥ c (2^(2 Re(ρ) − 1))^k. The constant may depend on ρ and works for every M. At Re(ρ) = 1/2 this gives a fixed positive lower bound on arbitrarily late shells. At Re(ρ) > 1/2 the lower bound grows as c (2^k)^(2 Re(ρ) − 1), with the full exponent 2 Re(ρ) − 1.

Put β = Re(ρ), γ = 2β − 1, q = 2^γ, and S(N) = Σ_{0 ≤ k < N} q^k. The theorem MobiusDyadicEnergy.signed_dyadic_eventual_prefix_lower_bound gives a rate r > 0 and a natural N₀ such that the sum of E(k) for k < N is at least r K(β, N log 2) for every N ≥ N₀. Here K(β,U) is the integral from 0 to U of exp(γt) dt. When β = 1/2, K(β,U) = U and K(β,N log 2) = (log 2) S(N). When β > 1/2, K(β,U) = (exp(γU) − 1)/γ and K(β,N log 2) = ((q − 1)/γ) S(N). Thus K(β,N log 2) = s S(N) with the indicated s > 0 in either case.

Take c = rs/2. If no shell k ≥ M has energy at least c q^k, split each prefix with N ≥ M into the finite head H = Σ_{0 ≤ k < M} E(k) and the tail M ≤ k < N. The prefix sum is at most H + c S(N), since all terms c q^k are nonnegative. Eventually H < c S(N). For q = 1 this follows from c S(N) = cN. For q > 1, put d = c/(q − 1) > 0. The quotient (H + d)/q^N tends to zero, so eventually H + d < d q^N and H < d(q^N − 1) = c S(N). Choose such an N with N ≥ M and N ≥ N₀. The upper bound is then strictly below 2c S(N), which is the prefix lower bound at that N.

## References

- Truth anchor: `D5/S3/Weil/Mertens/MobiusDyadicShellLower.exists_mobiusDyadicShellEnergy_ge_of_zero`
- Dependency: [D5/S3/Weil/Mertens/MobiusDyadicEnergy](MobiusDyadicEnergy.md)
