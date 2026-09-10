# Weil Arithmetic Fourier Dual Tail

## Abstract

An effective infinite-tail estimate for the actual arithmetic high-to-low Fourier readout, with a quadratic cutoff rate.

Use exactly s(c,n)=arithmeticBoundarySymbol from WeilArithmeticCouplingJet. It includes the finite von Mangoldt sum, poles and the absolutely convergent Gamma sine series. The independently proved envelope is B(c)=arithmeticBoundaryBudget(c). With m=M+j+1, DualTerm(j) equals ((n*s(c,n)-m*s(c,m))/(m^2-n^2)) / energy(j) / (m^2-w^2). All divisions by real scalars are cast into the complex field.

**Definition 1.1 (The concrete arithmetic dual summand).**

$$\operatorname{DualTerm}(c, n, M, energy, w, j)=\operatorname{div}(\operatorname{div}(\operatorname{div}({\operatorname{mul}(n, \operatorname{s}(c, n))-\operatorname{mul}(\operatorname{add}(M, j, 1), \operatorname{s}(c, \operatorname{add}(M, j, 1)))}, {\operatorname{square}(\operatorname{add}(M, j, 1))-\operatorname{square}(n)}), \operatorname{energy}(j)), {\operatorname{square}(\operatorname{add}(M, j, 1))-\operatorname{square}(w)})$$

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilArithmeticFourierDualTail.arithmeticEvenDualTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the collected even divided-difference coefficient multiplied by the complex Fourier Cauchy response and an inverse energy weight. It is defined independently of any desired bound or eigenfunction.

**Theorem 1.2 (Absolute convergence and a computable infinite remainder).**

$$\operatorname{And}(\operatorname{AtLeast}(c, 2), \operatorname{Less}(n, M), \operatorname{Positive}(beta), \operatorname{AllWeightsAtLeast}(energy, beta), \operatorname{LessEqual}(\operatorname{norm}(w), \operatorname{div}(M, 2)))\Rightarrow \operatorname{And}(\operatorname{SummableNorm}(\operatorname{DualTerm}(c, n, M, energy, w)), \operatorname{LessEqual}(\operatorname{norm}(\operatorname{tsum}(\operatorname{DualTerm}(c, n, M, energy, w))), \operatorname{div}(\operatorname{mul}(2, \operatorname{ArithmeticBudget}(c)), \operatorname{mul}(3, beta, M, {M-n}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilArithmeticFourierDualTail.arithmetic_even_fourier_dual_tail_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The arithmetic symbol bound is derived in the imported source, not assumed. For m>n>=0 it gives |(n*s_n-m*s_m)/(m^2-n^2)|<=B/(m-n). The complex restriction gives |m^2-w^2|>=3*m^2/4. Also m-n>=(M-n)*m/M. Therefore the summand is dominated by 4*B*M/(3*beta*(M-n))*m^(-3).

The positive telescoping inequality (x+1)^(-3)<=1/(2*x^2)-1/(2*(x+1)^2) proves both summability and sum_{m>M}m^(-3)<=1/(2*M^2). This is a genuine complete exterior series, not a finite terminal cutoff. No zero data, spectral gap, unknown operator norm or Xi convergence is an input.

In the actual phase-adjusted unnormalized cosine basis, multiply this bound by t_n*L^(3/2)*|z*sin(L*z/2)|/pi^3, where t_0=1, t_n=2 for n>0 and w=L*z/(2*pi). This bounds the missing component of C*D^(-1)g_Q. The checker uses this bound, exact binary endpoint sums and an interval LDL solve on the candidate-orthogonal space. The complex-disk zero count follows on paper from the resulting strict Rouche inequality. Operator identification, that numerical computation and the zero count are not conclusions of this Lean declaration.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticFourierDualTail.arithmeticEvenDualTerm`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticFourierDualTail.arithmetic_even_fourier_dual_tail_bound`
- Dependency: [D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet](WeilArithmeticCouplingJet.md)
