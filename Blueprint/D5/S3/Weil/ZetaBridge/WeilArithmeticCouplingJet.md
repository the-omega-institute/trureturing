# Weil Arithmetic Coupling Jet

## Abstract

The explicit pole, Gamma and finite-prime boundary symbol controls every exterior divided-difference coupling mode.

c is a natural number at least two, L=log(c), omega_n=2*pi*n/L, beta_j=2*j+1/2, and w_j=vonMangoldt(j)/sqrt(j). The symbol is s(c,n)=-2*omega_n*(cosh(L/2)-1)/(omega_n^2+1/4) -sum_{j>=0} omega_n*(1-exp(-beta_j*L))/(beta_j^2+omega_n^2) -sum_{j<c} w_j*sin(omega_n*log(j)). These are the actual boundary terms of the canonical arithmetic form. Their identification with its Fourier matrix follows the explicit calculations in Connes, Consani and Moscovici, arXiv:2511.22755, Lemma 2.3 and Section 4, and is a paper bridge in the existing source analysis.

**Definition 1.1 (The full arithmetic boundary symbol).**

$$\operatorname{s}(c, n)=\operatorname{PoleGammaPrimeSineExpression}(c, n)$$

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.arithmeticBoundarySymbol` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PoleGammaPrimeSineExpression is the explicit expression in the introductory paragraph. The prime cutoff is the integer c, with its endpoint omitted since the endpoint sine is zero. No zeta zero positions or lowest eigenvectors enter.

**Definition 1.2 (An independent arithmetic envelope).**

$$\operatorname{B}(c)=2 \operatorname{cosh}(\operatorname{HalfLog}(c))+\operatorname{AbsolutePrimeWeightSum}(c)$$

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.arithmeticBoundaryBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

HalfLog(c)=log(c)/2. AbsolutePrimeWeightSum(c) is the finite sum of |vonMangoldt(j)/sqrt(j)| over 0<=j<c. The two nonprime contributions are bounded by 2*(cosh(L/2)-1) and 2.

**Theorem 1.3 (Convergence and an unconditional arithmetic symbol bound).**

$$\operatorname{AtLeastTwo}(c)\Rightarrow \operatorname{AbsoluteGammaSineSummability}(c, n)\land \operatorname{abs}(\operatorname{s}(c, n))\leq \operatorname{B}(c)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.arithmetic_boundary_symbol_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

n is any integer. The Gamma sine series is absolutely convergent and |s(c,n)|<=B(c). The proof majorizes its absolute terms by |omega|/((2*j+1/2)^2+omega^2), proves a telescoping bound on every partial sum, and then controls the pole and prime terms. It assumes no operator-norm bound, Gamma-tail sign, spectral gap or Riemann hypothesis.

**Definition 1.4 (The arithmetic exterior coupling column).**

$$\operatorname{Column}(c, S, v, m)=\operatorname{DividedDifferenceSum}(c, S, v, m)$$

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.couplingColumn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite set S of integers and v:Z->C, this is sum_{n in S} ((s(c,n)-s(c,m))/(pi*(m-n)))*v_n, with the real coefficient cast to C. Exterior modes in the theorem cannot equal an interior mode, so no denominator vanishes.

**Definition 1.5 (Retain the two boundary moments).**

$$\operatorname{Jet}(c, S, v, m)=\operatorname{BoundaryMomentJet}(c, S, v, m)$$

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.couplingFirstJet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The definition is sum_{n in S} ((s(c,n)-s(c,m))/(pi*m))*v_n. Collecting this finite sum gives (b0-s(c,m)*a0)/(pi*m), where a0=sum v_n and b0=sum s(c,n)*v_n. No boundary moment is required to vanish.

**Theorem 1.6 (An all-scale exterior coupling remainder).**

$$\operatorname{AtLeastTwo}(c)\land \operatorname{Nonnegative}(N)\land \operatorname{InteriorIndicesBounded}(S, N)\land \operatorname{Exterior}(m, N)\Rightarrow \operatorname{norm}(\operatorname{Column}(c, S, v, m)-\operatorname{Jet}(c, S, v, m))\leq \operatorname{div}(2 \operatorname{B}(c) N, pi \operatorname{abs}(m) {\operatorname{abs}(m)-N}) \operatorname{NormMass}(S, v)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.arithmetic_coupling_first_jet_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

N is real and nonnegative, every n in S satisfies |n|<=N, and Exterior(m,N) means N<|m|. NormMass(S,v)=sum_{n in S}|v_n|. The coefficient difference is exactly (s(c,n)-s(c,m))*n/(pi*m*(m-n)). The arithmetic envelope and |m-n|>=|m|-N prove the displayed estimate. There is no upper exterior cutoff. The infinite Gram tail bound, the verified interval inequalities at c=3, and the resulting paper/computer-assisted full-space simple-even statement are documented separately; they are not asserted as Lean results of this declaration. No unbounded-scale ground-mode convergence to Xi is proved.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.arithmeticBoundaryBudget`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.arithmeticBoundarySymbol`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.arithmetic_boundary_symbol_bound`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.arithmetic_coupling_first_jet_error`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.couplingColumn`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.couplingFirstJet`
