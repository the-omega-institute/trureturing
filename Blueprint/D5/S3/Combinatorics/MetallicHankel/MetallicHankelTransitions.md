# Integral Metallic Continuant Approximations

## Abstract

The quadratic tail cycle produces integral continuants with prescribed degrees and leading approximation errors.

**Theorem 1.1 (The continuant approximation and its leading error).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelTransitions.metallic_approximation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MetallicHankel/MetallicHankelTransitions.metallic_approximation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

Let n be at least two and let a_p start at v_2 and follow the quadratic state transitions. Read k_p,b_p,D_p from its fraction data, and put v_0 = 1 and v_p = b_p for positive p. Assume s_0 = 0, s_{p+1} = s_p+k_p+1, h_0 = v_0 and h_{p+1} = h_p v_{p+1}. Let Q_0 = 1, Q_1 = D_0, N_0 = 0 and N_1 = v_0 q^{k_0}. Both continuants Y = Q and Y = N satisfy Y_{p+2} = D_{p+1}Y_{p+1} - v_{p+1}q^{k_p+k_{p+1}+2}Y_p. There exists a family of integral formal power series F_p such that q^{n+2} F_0^2 + T F_0 = q^{n-1}, where T = q(1-q^n)/(1-q) + (1+q^n)(1-q). Every Q_p has constant coefficient one and coefficients above degree s_p equal to zero; every N_p has coefficients at degrees at least s_p equal to zero. For every p there is an integral formal power series R_p with Q_p F_0 - N_p = q^{2s_p+k_p}R_p and constant coefficient h_p. Thus the error includes its exact leading coefficient.

## References

- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelTransitions.metallic_approximation`
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelData](MetallicHankelData.md)
