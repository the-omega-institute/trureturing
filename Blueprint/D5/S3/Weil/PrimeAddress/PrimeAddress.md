# Prime Address Residues

## Abstract

Five prime-address residues connect finite Euler modifications, amplitudes, ramified silence, and loud zeta addresses.

**Theorem 1.1 (Finite prime modifications preserve the global nontrivial zero set).**

$$\forall S : \operatorname{Finset} \mathbb{N}, (\forall p\in S, \operatorname{Prime}(p)) \Rightarrow \forall s : \mathbb{C}, \operatorname{IsNontrivialZero}(s) \Leftrightarrow (\operatorname{finitePrimeModification}(S, s) = 0 \land 0 < \Re(s) \land \Re(s) < 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/PrimeAddress/PrimeAddress.finite_prime_modification_preserves_global_zero_set` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite set of prime local factors, the modified zeta value vanishes exactly when classical zeta vanishes at every nontrivial zero. The proof uses the frozen finite Euler window zero-free theorem.

**Theorem 1.2 (Prime-seven deletion is the finite-modification instance).**

$$\forall s : \mathbb{C}, \operatorname{IsNontrivialZero}(s) \Leftrightarrow (\operatorname{finitePrimeModification}(\{7\}, s) = 0 \land 0 < \Re(s) \land \Re(s) < 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/PrimeAddress/PrimeAddress.prime_seven_deletion_preserves_nontrivial_zeta_zeros` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This theorem is obtained by instantiating the preceding general result with the singleton prime set containing seven.

**Theorem 1.3 (A positive-real zero contribution has cosine amplitude).**

$$\forall x, \beta, \gamma \in \mathbb{R}, 0 < x \Rightarrow \Re((x : \mathbb{C})^{(\beta : \mathbb{C}) + (\gamma : \mathbb{C}) * i}) = x^\beta * \operatorname{cos}(\gamma * \operatorname{log}(x)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/PrimeAddress/PrimeAddress.zero_contribution_amplitude_x_beta_cos_gamma_log_x` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive base x, the real part of the complex power with exponent beta plus i gamma is x to the beta times cos(gamma log x).

**Theorem 1.4 (Dirichlet characters silence primes ramified by the modulus).**

$$\forall R : Type, [\operatorname{CommMonoidWithZero} R], \forall q \in \mathbb{N}, \forall chi : \operatorname{DirichletCharacter}(R, q), \forall p \in \mathbb{N}, \operatorname{Prime}(p) \land p \mid q \Rightarrow chi((p : \operatorname{ZMod} q)) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/PrimeAddress/PrimeAddress.dirichlet_l_functions_silence_ramified_primes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Dirichlet character maps a prime residue to zero whenever that prime divides the modulus, by the nonunit mapping law and the ZMod coprimality criterion.

**Theorem 1.5 (Every zeta prime address is loud).**

$$\forall p, k \in \mathbb{N}, \operatorname{Prime}(p) \land k \neq 0 \Rightarrow \operatorname{singleAddressReading}(p^k) \neq 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/PrimeAddress/PrimeAddress.zeta_has_no_silent_prime_address` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen single-address reading gives log p at a prime power, and Real.log_pos makes this nonzero for every prime.

## References

- Truth anchor: `D5/S3/Weil/PrimeAddress/PrimeAddress.dirichlet_l_functions_silence_ramified_primes`
- Truth anchor: `D5/S3/Weil/PrimeAddress/PrimeAddress.finite_prime_modification_preserves_global_zero_set`
- Truth anchor: `D5/S3/Weil/PrimeAddress/PrimeAddress.prime_seven_deletion_preserves_nontrivial_zeta_zeros`
- Truth anchor: `D5/S3/Weil/PrimeAddress/PrimeAddress.zero_contribution_amplitude_x_beta_cos_gamma_log_x`
- Truth anchor: `D5/S3/Weil/PrimeAddress/PrimeAddress.zeta_has_no_silent_prime_address`
- Dependency: [D5/S3/Weil/EulerProduct](../EulerProduct.md)
- Dependency: [D5/S3/Zeros/EulerWindows](../../Zeros/EulerWindows.md)
