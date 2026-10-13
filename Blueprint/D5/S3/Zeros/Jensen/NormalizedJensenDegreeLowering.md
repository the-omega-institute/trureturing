# Normalized Jensen Degree Lowering

## Abstract

Fixed theta-moment Jensen polynomials satisfy exact degree lowering.

**Definition 1.1 (Fixed even theta kernel).**

$$\forall x\in\mathbb{R}, K\left(x\right)=\sum'_{n\in\mathbb{N}} (4 \pi^{2} (n+1)^{4} \exp\left(\frac{9 |x|}{2}\right)-6 \pi (n+1)^{2} \exp\left(\frac{5 |x|}{2}\right)) \exp\left(-\pi (n+1)^{2} \exp\left(2 |x|\right)\right)$$

*Formalization.* `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.sourceThetaKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

K denotes sourceThetaKernel. The natural index starts at zero, so n+1 runs over the positive integers. Absolute value specifies the even extension of the positive half-line expression. The primed sum denotes Lean's totalized tsum; this definition asserts no convergence theorem.

**Definition 1.2 (Fixed density expression).**

$$\forall x\in\mathbb{R}, p\left(x\right)=\frac{K\left(x\right)}{\Re\left(xiReading\left(\frac{1}{2}\right)\right)}$$

*Formalization.* `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.sourceThetaDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

p denotes sourceThetaDensity, with the real part of the frozen xiReading at one half as its exact denominator. Private checked consequences of xi_reading_conj identify that real part with the complex central value and identify the complex coercion of p with K divided by that value. No nonzero-denominator or probability-mass theorem is asserted.

**Definition 1.3 (Even density moments).**

$$\forall k\in\mathbb{N}, m_{2 k}=\int_{\mathbb{R}} x^{2 k} p\left(x\right)\,dx$$

*Formalization.* `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.sourceThetaMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sourceThetaMoment(k) is m at index 2k. The integral is the real Lebesgue integral of x^(2k) times the displayed density. It uses Lean's totalized integral and does not assert integrability.

**Definition 1.4 (Fixed moment coefficients).**

$$\forall k\in\mathbb{N}, a_{k}=\frac{m_{2 k}}{(2 k)!}$$

*Formalization.* `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.sourceThetaCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

a denotes the fixed sequence sourceThetaCoefficient. Its denominator is (2k)!, not k!. No Taylor-coefficient correspondence or assertion that a at zero is one is used.

**Definition 1.5 (Canonical Jensen adapter).**

$$\forall b:\mathbb{N}\to\mathbb{R}, \forall d\in\mathbb{N}, N\left(b, d\right)=\operatorname{map}_{\mathbb{R}\to\mathbb{C}}\left(J\left(k\mapsto k! b_{k}, d, 0\right)\circ(\frac{1}{d} X)\right)$$

*Formalization.* `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.normalizedJensen` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

N(b,d) denotes normalizedJensen b d for any real coefficient sequence b. J is the frozen jensenPolynomial: its coefficients are choose(d,k) times gamma(n+k), for k from zero through d. Here gamma(k)=k!b(k), the shift is zero, and polynomial composition scales the variable by the real inverse of d. The final map is the coefficient embedding from real to complex polynomials. X is the polynomial indeterminate.

**Definition 1.6 (Independent finite source polynomial).**

$$\forall d\in\mathbb{N}, P_{d}=\sum_{k=0}^{d} \frac{descFactorial\left(d, k\right)}{d^{k}} a_{k} X^{k}$$

*Formalization.* `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.sourceJensenPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

P at index d denotes sourceJensenPolynomial d, defined independently by this finite sum in Complex[X]. descFactorial(d,k) is the natural falling factorial d(d-1)...(d-k+1), with value one at k=0; its quotient by d^k is the prescribed weight. Natural factors and real coefficients are coerced to Complex. The upper limit is exactly d.

**Theorem 1.7 (Exact canonical normalization).**

$$\forall b:\mathbb{N}\to\mathbb{R}, \forall d\in\mathbb{N}, 1\leq d\Rightarrow N\left(b, d\right)=\sum_{k=0}^{d} \frac{descFactorial\left(d, k\right)}{d^{k}} b_{k} X^{k}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.normalizedJensen_eq_fallingFactorial_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real sequence and every natural d at least one, the canonical adapter equals the finite falling-factorial sum. The proof distributes composition and coefficient mapping and uses the exact identity descFactorial(d,k)=k! choose(d,k).

**Theorem 1.8 (Universal polynomial degree lowering).**

$$\begin{aligned}\forall b:\mathbb{N}\to\mathbb{R}, \forall d\in\mathbb{N}, 2\leq d\Rightarrow \\N\left(b, d\right)-\frac{1}{d} X N\left(b, d\right)'=N\left(b, d-1\right)\circ(\frac{d-1}{d} X)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.normalizedJensen_degree_lowering` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is an equality of complex polynomials for every real sequence b. The prime denotes Polynomial.derivative and the circle denotes polynomial composition. Comparing coefficients reduces it to the falling-factorial recurrence, including the top index k=d and all indices beyond d. The degree bound makes both d and d-1 nonzero.

A same-source analytic application uses T_n f with coefficients ((n)_k/n^k) f^(k)(0)/k!, for n nonzero and k from zero through n. For a complex smooth source preserving the real axis, derivative uniqueness identifies these complex jets with the embedded jets of its real restriction. The preceding canonical normalization theorem therefore identifies T_n f with normalizedJensen at that exact jet sequence. This identification does not assert that the fixed theta-density moments above already equal the jets of the actual xi source.

The same coefficient recurrence gives T_n(zf) = t T_n f - (t^2/n)(T_n f)' and (T_n f)' = T_n(f') - (t/n)(T_n(f'))'. The top coefficient cancels in the second identity. Consequently, multiplication by z-a acts by L_a P = (t-a)P - (t^2/n)P'. Applying this exact operator twice extracts f(z) = (z-a_2)(z-a_1) Ahat(z), while source differentiation gives T_n(f') = L_a1 Hhat + L_a2(Hhat + L_a1 Vhat). Here Hhat = T_n Ahat and Vhat = T_n(Ahat'); the second response extracts the source derivative and is distinct from the derivative of the first response.

For the original selection, regroup Q = Qfar Qcore and Ahat = A Qfar, with Qcore(z) = (z-a_1)(z-a_2). The far polynomial may have arbitrary degree and the real roots a_1 and a_2 may coincide, so both multiplicities remain present. The complete original source is f = A Qfar Qcore. Put J = T_n f, G = T_n(f'), H = T_n A and V = T_n(A'). On H nonzero, retain the original responses P = J/H and S = G/H - (V/H)P.

On Hhat nonzero, set v = t^2/n, ell = Hhat'/Hhat, s = Vhat/Hhat, chi = t-v ell and eta = 1-v s'. These are derived from the same extracted source. With m = (a_1+a_2)/2, delta = (a_1-a_2)/2, x = chi-m and U = v chi', the exact core identities are p = x^2-delta^2-U, p' = 2x chi'-U' and w = 2 eta x-v eta'. Thus J = Hhat p and G = Hhat(s p+w).

At a real actual node J(t)=0, assume H and Hhat nonzero, v>0, chi'>1/2, eta>1/2, |U'|<sqrt(v)/8 and |v eta'|<sqrt(v)/8. The node forces x^2 = delta^2+v chi' >= v/2. Both core responses have the sign of x and magnitude greater than 3|x|/4, which gives p'w > x^2/2 >= v/4. The exact original amplitude identity is H^2 P'S = J'G = Hhat^2 p'w, hence P'S > (1/4)(Hhat/H)^2 v. In the complex source application the same real-node product has zero imaginary part and positive real part; the node is simple.

This conditional quadratic-core application uses the existing normalization, iterated derivative product rule, quotient rule and ordered-field estimates. It introduces no independent root-preservation or convolution theorem. Applying it to the actual xi source still requires its analytic factorization and jet correspondence, the local all-critical premise, exterior response estimates and central total multiplicity at most two. It does not establish arbitrary growing-core positivity, all-height exclusion, RH or strict Robin for every integer above 5040.

The same-source application also treats a core of exactly three real source roots a_1,a_2,a_3, including repeated roots. Retain Ahat=A Qfar with no degree restriction on Qfar, and extract f=(z-a_3)(z-a_2)(z-a_1) Ahat. Three applications of L_a give J=L_a3 L_a2 L_a1 Hhat. Source differentiation gives G=L_a2 L_a1 Hhat+L_a3(L_a1 Hhat+L_a2(Hhat+L_a1 Vhat)); it is the extraction of f', with the same exterior and far factor.

Put m=(a_1+a_2+a_3)/3, beta_i=a_i-m, a=sum(beta_i^2)/6 and b=beta_1 beta_2 beta_3. The real-source discriminant gives a>=0 and |b|<=2a sqrt(a), even when roots coincide. Set x=chi-m, U=v chi', V_3=v U', Z_3=v(v eta')' and M_3=3(x^2-a-U). Quotient and product differentiation of the actual Hhat,Vhat yields p_3=x^3-3(a+U)x-b+V_3, p_3'=chi' M_3-3U' x+V_3' and w_3=eta M_3-3v eta' x+Z_3. Thus J=Hhat p_3 and G=Hhat(s p_3+w_3). Both V_3 and Z_3 retain the noncommuting derivative terms.

For a>=0, u>0, |b|<=2a sqrt(a) and |e|<=u sqrt(u), an actual real root x of C(z)=z^3-3(a+u)z-b+e satisfies |C'(x)|>=(3/2)sqrt(u)(|x|+sqrt(a+u))>=(3/2)u. Indeed, with h=sqrt(a+u) and y=|x|, the source bounds give |b-e|<=2h^3-u h. The root equation forces y<2h and (y-h)^2(y+2h)>=u h, hence |y-h|>=sqrt(u)/2. Factoring |C'(x)|=3|y-h|(y+h) gives the stated margin. This pointwise comparison does not assume the roots have already been labeled or analytically continued.

At an actual real J-node, assume H and Hhat nonzero, v>0, sigma>0, |U-sigma^2|<sigma^2/32, |V_3|<sigma^3/32, |chi'-1|<1/64 and |eta-1|<=1/128. Also assume |U'|<sigma/256, |V_3'|<sigma^2/256, |v eta'|<sigma/256 and |Z_3|<sigma^2/256. Applying the cubic slope bound at u=U,e=V_3 yields sigma |x|<=|M_3| and sigma^2<2|M_3|. Each response correction has magnitude below 5|M_3|/256. Consequently p_3'/M_3 and w_3/M_3 exceed 1/2, and p_3'w_3>M_3^2/4>v^2/4. The original identity H^2 P'S=J'G=Hhat^2 p_3'w_3 therefore gives P'S>(1/4)(Hhat/H)^2 v^2>0.

This cubic real-node application remains conditional on the complete exterior jet estimates, actual xi factorization and jet correspondence, the local all-critical premise and central total multiplicity exactly three. It does not prove moving complex-root branches, target-disc node counts, endpoint existence criteria or uniform growing-core control. Those interfaces, all-height exclusion, RH and strict Robin above 5040 remain unresolved by this application.

For the fixed reference cubic Cstar(z)=z^3-3(a+sigma^2)z-b, assume a>=0, sigma>0 and |b|<=2a sqrt(a). Writing h=sqrt(a+sigma^2), the endpoint signs and the intermediate value theorem construct roots in (-2h,-h), (-h,h) and (h,2h). The preceding slope comparison gives distance at least sigma/2 from either adjacent critical point, hence both adjacent reference-root gaps are at least sigma. No root labels are imposed as hypotheses.

For each fixed complex U and V_3 with |U-sigma^2|<sigma^2/32 and |V_3|<sigma^3/32, compare C(z)=z^3-3(a+U)z-b+V_3 with Cstar on the fixed square around each reference root, of halfwidth sigma/12. The square lies strictly inside the sigma/8 disc, and its border is at distance at least sigma/12 from the center. Factoring Cstar and using the reference slope gives the border lower bound (147/1536)sigma^2(|lambda|+h), strictly exceeding the original perturbation budget (3/32)sigma^2(|lambda|+h). The existing rectangle Rouche zero-count supplier therefore gives one unique simple C-zero in each square.

These three zeros are distinct and satisfy |s_j-lambda_j|<sigma/8. Their actual root equations imply the complete identity C(z)=(z-s_1)(z-s_2)(z-s_3) at every complex z. This is a pointwise construction for every allowed pair U,V_3; neither the zeros nor the factorization are assumed. It reuses the same scalar comparison and existing complex analytic zero count.

For real selected a,b,c, let Ahat(z)=B(z)Qfar(z), F(z)=(z-c)(z-b)(z-a)Ahat(z), H=T_n Ahat, Vhat=T_n Ahat', J=T_n F, and G=T_n F'. Here n is nonzero, Qfar is an arbitrary complex polynomial and B is supplied ContDiff over C. These are the actual complete sources of the finite extraction, not independently chosen responses. At each H(t)!=0 the checked polynomial identities give J=H P, J'=H' P+H P1 and G=H(S P+W), with all rational jets taken from this same H,Vhat. The checked jet identities and the open H!=0 neighborhood prove that the actual chi,U,V3,eta are analytic at t.

The sigma/12 fixed-box unique roots glue through local implicit uniqueness to three labels lambda_j of the same cubic for every good complex parameter. The original amplitude budgets |U-sigma^2|<sigma^2/32 and |V3|<sigma^3/32 imply |lambda_j-l_j|<sigma/8 and exact cubic factorization for every complex z. Reference gaps and moving gaps give |lambda'_j|<1/54<1/32 from |U'|<sigma/256 and |V3'|<sigma^2/256; no separate derivative margin is assumed. Actual U,V3 conjugation identities imply conjugation of these same constructed labels.

For a convex conjugation-invariant complex set S, retain H!=0, the original amplitude and derivative budgets, |chi'-1|<1/64 and the actual-source conjugation identities throughout S. The actually constructed coordinate branches f_j=chi-m-lambda_j are analytic and injective on the whole S, including its boundary. Each branch node is real and simple, and distinct branches share no node. The complete extraction satisfies J(t)=H(t)f1(t)f2(t)f3(t) on S. Consequently its actual J zero set on S is finite, all its zeros are real and simple and its cardinality is at most three. Finiteness and this count are conclusions from the three injective branches, not premises.

At each t in S, analyticity and the strict original U,V_3 amplitude budgets extend the same constructed-label factorization to a neighborhood of t. H(t)!=0 also extends locally, so the complete actual-source identity gives J=H f1 f2 f3 on that neighborhood. Additivity of analytic order, the simple branch nodes and absence of shared nodes therefore give analyticOrderNatAt(J,t)=1 at every actual J zero, including a boundary point of S. No openness of S or additional margin hypothesis is required.

When the complex source B has a supplied smooth real restriction f, B(x)=f(x) on the real axis, and Qfar is mapped from a real polynomial, the iterated derivatives at zero agree with the real-source derivatives by uniqueness. Thus the actual H is the map of the same real finite extraction. The explicit quotient jets chi,U,V3 commute with conjugation at every complex parameter, including a zero of H under totalized division. This supplies all three coordinate conjugation identities used above. Under the same six uniform nonzero, value and derivative budgets, the same actual J therefore has real simple zeros and cardinality at most three on the entire closed target S; no separate coordinate analyticity or conjugation premise is needed. The real source realization and the numerical source budgets remain explicit conditions.

These applications use standard pinned complex analytic, implicit-function, zero-count, mean-value and set-cardinality results. They are bind-only with admission_basis none and are recorded here as source-derived applications rather than new retained D5 declarations. The canonical xi B/F identity and payment of the uniform actual-source nonvanishing, amplitude and derivative budgets remain open; no RH, strict Robin beyond 5040 or global root-reality conclusion follows from this conditional local reduction.

**Theorem 1.9 (Source and canonical polynomial equality).**

$$\forall d\in\mathbb{N}, 1\leq d\Rightarrow P_{d}=N\left(a, d\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.sourceJensenPolynomial_eq_normalizedJensen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The independent literal source polynomial equals the canonical adapter at the fixed density-moment coefficient sequence. This is the preceding normalization theorem specialized to a and read in the reverse direction.

**Theorem 1.10 (Exact source degree lowering at every complex argument).**

$$\begin{aligned}\forall d\in\mathbb{N}, 2\leq d\Rightarrow \forall v\in\mathbb{C}, \\P_{d}\left(v\right)-\frac{v}{d} P_{d}'\left(v\right)=P_{d-1}\left(\frac{d-1}{d} v\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.source_jensen_degree_lowering` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

P'(v) means Polynomial.derivative evaluated at v. The proof uses the named source-to-canonical equality at d and d-1, then evaluates the universal lowering identity at v. All subtraction of natural degrees is interpreted in Nat before coercion; d at least two supplies the required bounds. No root-reality, RH, positivity, analytic convergence, or exact polynomial-degree premise is imposed.

## References

- Truth anchor: `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.normalizedJensen`
- Truth anchor: `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.normalizedJensen_degree_lowering`
- Truth anchor: `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.normalizedJensen_eq_fallingFactorial_sum`
- Truth anchor: `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.sourceJensenPolynomial`
- Truth anchor: `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.sourceJensenPolynomial_eq_normalizedJensen`
- Truth anchor: `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.sourceThetaCoefficient`
- Truth anchor: `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.sourceThetaDensity`
- Truth anchor: `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.sourceThetaKernel`
- Truth anchor: `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.sourceThetaMoment`
- Truth anchor: `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.source_jensen_degree_lowering`
- Dependency: [D5/S3/Zeros/Jensen/JensenPolynomialObstruction](JensenPolynomialObstruction.md)
- Dependency: [D5/S3/Zeros/Symmetry/ZetaConjugationCovariance](../Symmetry/ZetaConjugationCovariance.md)
