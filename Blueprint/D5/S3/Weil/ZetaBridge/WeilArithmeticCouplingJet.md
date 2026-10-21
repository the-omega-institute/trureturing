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

SOURCE_ONLY_UNCOMPILED candidate: the smooth-weight descriptions below belong to WeilArithmeticCouplingJet and retain the actual native operands. They use the existing pole and convergent Gamma series, with w(c,m)=(P(c,m)+G(c,m))/m^2=H(c,m)/m^2 and A=-H-S. Fresh source bindings, Scribe emission and faithful Reg registration remain caller-owned obligations for the changed source hash.

**Definition 1.7 (The two actual Gamma bounds in one minimum).**

$$\operatorname{E}(c, m)=\operatorname{min}(2+\operatorname{div}(\operatorname{U}(c), m), \operatorname{div}(pi, 4)+\operatorname{div}(\operatorname{U}(c)+\operatorname{div}(3, 4 \operatorname{a}(c)), m))$$

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.smoothEnvelope` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural c,m this is exactly min(2+U(c)/m,pi/4+(U(c)+3/(4*a(c)))/m). Here L=log(c), a=2*pi/L and U=2*(cosh(L/2)-1)/a. Lean division is total; the estimates below use positive modes and c>=2. This is a finite envelope at every positive mode. Its fixed-c limit pi/4 and the corresponding square coefficient pi^2/16 are asymptotic interpretations still requiring real scoped verification; they are not new Lean limit theorems.

**Definition 1.8 (The actual nonnegative smooth weight).**

$$\operatorname{w}(c, m)=\operatorname{div}(\operatorname{P}(c, m)+\operatorname{G}(c, m), \operatorname{square}(m))$$

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.smoothWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

P is exactly poleSine(L,frequency(c,m)); G is exactly tsum_j gammaSineTerm(L,frequency(c,m),j) from the native owner. Thus H=P+G=m^2*w and A=-H-S, with H the positive smooth mass and no new Gamma object. This definition is not a claim that Gamma itself is monotone.

**Theorem 1.9 (Nonnegativity after division by the mode square).**

$$\operatorname{AtLeastTwo}(c)\land\operatorname{Positive}(m)\Rightarrow\operatorname{Nonnegative}(\operatorname{w}(c, m))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.smooth_weight_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural c>=2 and m>0, 0<=w(c,m). The factors 1-exp(-(2*j+1/2)*log(c)) and cosh(log(c)/2)-1 are nonnegative. The actual convergent Gamma sum is retained.

**Theorem 1.10 (Antitonicity of the actual smooth weight).**

$$\operatorname{AtLeastTwo}(c)\land\operatorname{Positive}(n)\land n\leq m\Rightarrow\operatorname{w}(c, m)\leq\operatorname{w}(c, n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.smooth_weight_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural c>=2 and 0<n<=m, w(c,m)<=w(c,n). Each normalized Gamma summand is a nonnegative constant divided by m*((2*j+1/2)^2+a^2*m^2). The pole has the same form with r^2=1/4. Compare positive denominators and use the two actually summable divided Gamma series; no differentiation or divergent interchange occurs.

**Theorem 1.11 (The minimum envelope at every later positive mode).**

$$\operatorname{AtLeastTwo}(c)\land\operatorname{Positive}(n)\land n\leq m\Rightarrow\operatorname{Nonnegative}(\operatorname{E}(c, n))\land\operatorname{square}(m) \operatorname{w}(c, m)\leq\operatorname{E}(c, n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.smooth_weight_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural c>=2 and 0<n<=m, 0<=E(c,n) and m^2*w(c,m)<=E(c,n). The old Gamma <=2 and the new Gamma <=pi/4+3/(4*a*m) bounds are both consumed, at positive frequency omega=a*m. The new private proof uses f(x)=omega/(omega^2+x^2) and g(t)=f(2*t+1/2). Pinned AntitoneOn.sum_le_integral compares each finite shifted lattice sum with its interval integral. Pinned intervalIntegral.mul_integral_comp_mul_add and integral_div_sq_add_sq give twice that integral as arctan((2*M+1/2)/omega)-arctan((1/2)/omega). Antitonicity of f gives arctan((1/2)/omega)>=f(1/2)/2, so the complete partial sum is <=pi/4+3*f(1/2)/4<=pi/4+3/(4*omega). The original summability and actual sine-factor majorization pass this to the genuine Gamma tsum for log(c)>=0. No monotonicity of Gamma mass is used, and no cutoff restriction is added. This complete source attempt remains SOURCE_ONLY_UNCOMPILED.

SOURCE_ONLY_UNCOMPILED finite-block addition. Here H(c,m)=m^2*smoothWeight(c,m) is the POSITIVE smooth mass and the actual symbol is A=-H-S, where S is the existing finite-prime sine sum. This fixes the sign convention for all smooth-weight descriptions using the same positive-H convention.

**Definition 1.12 (An explicit smooth-mass floor).**

$$\operatorname{smoothFloor}(c)=\operatorname{div}(1-\operatorname{exp}(\operatorname{div}(-\operatorname{logLength}(c), 2)), 10)$$

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.smoothFloor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural c, smoothFloor(c)=(1-exp(-logLength(c)/2))/10, with logLength(c)=log(c). It is strictly positive under c>=2. This is an explicit finite-block lower constant; no sharp asymptotic value is asserted.

**Theorem 1.13 (A positive floor for the actual pole plus Gamma mass).**

$$\operatorname{AtLeastTwo}(c)\land \operatorname{Positive}(m)\land 1\leq \operatorname{omega}(c, m)\Rightarrow \operatorname{Positive}(\operatorname{smoothFloor}(c))\land \operatorname{smoothFloor}(c)\leq \operatorname{square}(m) \operatorname{smoothWeight}(c, m)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.smooth_weight_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact telescope is {c m : Nat}, hc:2<=c, hm:0<m, hw:1<=frequency(c,(m:Int)). Here omega(c,m) denotes exactly that frequency. The conclusion retains both 0<smoothFloor(c) and smoothFloor(c)<=m^2*smoothWeight(c,m), for every such c and m. The weight is the original poleSine plus the actual convergent gammaSineTerm series, divided by m^2.

Fix the actual L=logLength(c)>0 and w=omega(c,m)>=1. Put eta=1-exp(-L/2)>0 and N=Nat.ceil(w). For each j<N, Nat.lt_ceil gives j<w, so 1/2<=gammaRate(j)<=3*w and gammaRate(j)^2+w^2<=10*w^2. Exponential monotonicity gives 1-exp(-gammaRate(j)*L)>=eta. Two positive division comparisons, one for the denominator and one for the numerator, give gammaSineTerm(L,w,j)>=eta/(10*w). Nat.le_ceil gives w<=N, so this finite block has sum at least eta/10. Only then Summable.sum_le_tsum, using gamma_positive_summable and gamma_positive_nonneg, passes to the genuine owner Gamma sum. The pole is nonnegative by cosh(L/2)>=1 and w>=1; cancellation of the positive mode square uses the shared owner smooth_mass_eq identity.

The source-level new content is a lower bound obtained by a block whose length depends on the actual frequency; it is not a binding wrapper around an existing floor theorem. At c=2 this supplies the positive smooth mass needed by the beta-only lower-tail route, where the separate finite-prime sine sum vanishes. No separate c=2 or eventual specialization is added. For larger c, possible cancellation with S is not controlled by this theorem. No pi/4 asymptotics, full-symbol pointwise lower bound, operator positivity, Robin statement, RH statement or five-mode identification is claimed. Lean elaboration, kernel checking, registration binding, Scribe emission and official required checks remain unperformed.

**Theorem 1.14 (The actual smooth mass has a pi/4 asymptotic with an explicit rate).**

$$\forall c\in\mathbb{N}, 2\le c\Rightarrow \exists K\in\mathbb{R}, 0<K\land \forall m\in\mathbb{N}, 0<m\Rightarrow \lvert m^{2}\cdot\operatorname{smoothWeight}(c, m)-\frac{\pi}{4}\rvert\le\frac{K}{m}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.smooth_weight_actual_asymptotic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural c with hc:2<=c there exists one real K>0, depending only on c, such that for every natural m>0, abs(m^2*smoothWeight(c,m)-pi/4)<=K/m. The selected declaration retains the actual poleSine and the genuinely convergent gammaSineTerm series in their original owner. It has no frequency threshold and includes m=1.

Write L=log(c)>0, a=2*pi/L>0, w=a*m, C=exp(-L/2)/(1-exp(-2*L)), and U=2*(cosh(L/2)-1)/a. The existential proof takes K=explicitSmoothK(c)=U+(1+C)/a and reuses explicitSmoothK_spec before introducing m. The half-shifted Cauchy majorant has sum at least pi/4-1/(4*w), by left-endpoint integral comparison, the exact finite arctan substitution and its pi/2 endpoint limit. Mathlib's arctan_le_self bounds the initial shift error. The removed nonnegative exponential correction is truly summable and at most exp(-L/2)/(w*(1-exp(-2*L))), by a positive geometric majorant. Subtraction uses both summability hypotheses. Combining that lower bound with the existing smooth_mass_bounds upper estimate proves the absolute bound.

For each fixed c at least 2, the constant K is chosen before m. The estimate holds for every positive natural m, including m=1. It gives no constant uniform in c and by itself establishes neither a coefficient-uniform tail bound nor RH.

**Definition 1.15 (An explicit constant for the complete smooth mass).**

$$\operatorname{K}(c)=\operatorname{div}(2 \operatorname{coshMinusOne}(\operatorname{HalfLog}(c))+1+\operatorname{GammaCorrection}(c), \operatorname{a}(c))$$

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.explicitSmoothK` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For L=log(c), a=2*pi/L and C=exp(-L/2)/(1-exp(-2*L)), K(c)=(2*(cosh(L/2)-1)+1+C)/a. GammaCorrection denotes exactly C, and cosh-minus-one(x) denotes cosh(x)-1. This formula fixes K from c alone, with the entire exponential correction and pole term.

**Theorem 1.16 (The specified constant controls every positive mode).**

$$\operatorname{AtLeastTwo}(c)\Rightarrow\operatorname{Positive}(\operatorname{K}(c))\land\forall m\in\mathbb{N}, \operatorname{Positive}(m)\Rightarrow\lvert m^{2}\cdot\operatorname{smoothWeight}(c, m)-\frac{\pi}{4}\rvert\leq\frac{\operatorname{K}(c)}{m}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.explicitSmoothK_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural c>=2, K(c)>0 and the absolute error is at most K(c)/m for every positive natural m. The complete pole plus the convergent Gamma series remain in smoothWeight. The upper mass bound and the lower Gamma estimate use the same explicit constant. This specification also proves smooth_weight_actual_asymptotic. There is no lower frequency threshold; c=2 and m=1 are included.

**Theorem 1.17 (A cutoff bound for the same explicit constant).**

$$\operatorname{AtLeastThree}(c)\Rightarrow\operatorname{K}(c)\leq\operatorname{sqrt}(c) \operatorname{logLength}(c)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.explicitSmoothK_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural c>=3, K(c)<=sqrt(c)*log(c). Put s=sqrt(c). Then exp(-L/2)=1/s, exp(-2*L)=1/c^2 and 2*(cosh(L/2)-1)+1=s+1/s-1<=s. The correction (1/s)/(1-1/c^2) is at most s, so the numerator is at most 2*s. Division by 2*pi/L and pi>=1 give the stated bound. This uses the same K as the all-positive-mode estimate above.

**Theorem 1.18 (The exact native smooth and prime split).**

$$\operatorname{Positive}(m)\Rightarrow\operatorname{A}(c, m)=-\operatorname{square}(m) \operatorname{w}(c, m)-\operatorname{OwnerPrimeRangeSum}(c, m)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.arithmetic_symbol_smooth_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural c and positive natural m, A(c,m)=-m^2*w(c,m)-sum_{q<c} primeWeight(q)*sin(frequency(c,m)*log(q)). No c>=2 assumption is needed for this identity. The downstream module uses the existing owner_prime_sum_eq to identify the finite range sum with T2.primeSymbol.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.arithmeticBoundaryBudget`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.arithmeticBoundarySymbol`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.arithmetic_boundary_symbol_bound`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.arithmetic_coupling_first_jet_error`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.arithmetic_symbol_smooth_split`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.couplingColumn`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.couplingFirstJet`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.explicitSmoothK`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.explicitSmoothK_le`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.explicitSmoothK_spec`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.smoothEnvelope`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.smoothFloor`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.smoothWeight`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.smooth_weight_actual_asymptotic`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.smooth_weight_antitone`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.smooth_weight_envelope`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.smooth_weight_floor`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.smooth_weight_nonneg`
