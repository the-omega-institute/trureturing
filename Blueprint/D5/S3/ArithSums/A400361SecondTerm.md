# A400361: the second-order summatory constant

## Abstract

The exact second-order summatory formula for the Pillai minus floor-gcd sequence.

For positive integers n, let P(n) be the sum of gcd(n,k) over 1 <= k <= n, and let F(n) be the sum of gcd(n,floor(n/k)) over the same range. OEIS A400361 revision 17 conjectures the full second-order summatory formula for a(n)=P(n)-F(n). All differences are signed. The statement below retains every positive integer index and the literal digamma, totient, and zeta-derivative constant.

**Definition 1.1 (The floor-gcd sum).**

$$\forall n \in \operatorname{Nat}\left(\right), \operatorname{F}\left(n\right) = \sum_{k \in \operatorname{Icc}\left(1, n\right)} {\operatorname{gcd}\left(n, \operatorname{natDiv}\left(n, k\right)\right)}$$

*Formalization.* `D5/S3/ArithSums/A400361SecondTerm.floorGcd` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ctibor O. Zizka; OEIS Foundation Inc. (2026). *OEIS A400361 revision 17, the second-order Pillai minus floor-gcd conjecture*. URL: <https://oeis.org/A400361>.

*Commentary.*

natDiv is natural-number division, hence floor(n/k) for k>0. The range includes both endpoints. The sum is natural-valued.

**Definition 1.2 (The signed source sequence).**

$$\forall n \in \operatorname{Nat}\left(\right), \operatorname{a}\left(n\right) = \operatorname{toInt}\left(\operatorname{P}\left(n\right)\right) - \operatorname{toInt}\left(\operatorname{F}\left(n\right)\right)$$

*Formalization.* `D5/S3/ArithSums/A400361SecondTerm.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ctibor O. Zizka; OEIS Foundation Inc. (2026). *OEIS A400361 revision 17, the second-order Pillai minus floor-gcd conjecture*. URL: <https://oeis.org/A400361>.

*Commentary.*

P is Pillai's gcd-sum function. Symmetry of gcd identifies its gcd(k,n) convention with gcd(n,k). Both natural values are embedded in the integers before subtraction.

**Definition 1.3 (The real cumulative sum).**

$$\forall N \in \operatorname{Nat}\left(\right), \operatorname{S}\left(N\right) = \sum_{n \in \operatorname{Icc}\left(1, N\right)} {\operatorname{toReal}\left(\operatorname{a}\left(n\right)\right)}$$

*Formalization.* `D5/S3/ArithSums/A400361SecondTerm.S` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ctibor O. Zizka; OEIS Foundation Inc. (2026). *OEIS A400361 revision 17, the second-order Pillai minus floor-gcd conjecture*. URL: <https://oeis.org/A400361>.

*Commentary.*

The signed integer source values are cast to the reals. The sum at zero is empty; convergence at infinity retains all positive N.

**Definition 1.4 (The real digamma function).**

$$\forall x \in \operatorname{Real}\left(\right), \operatorname{psi}\left(x\right) = \frac{\operatorname{derivGamma}\left(x\right)}{\operatorname{Gamma}\left(x\right)}$$

*Formalization.* `D5/S3/ArithSums/A400361SecondTerm.realDigamma` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ctibor O. Zizka; OEIS Foundation Inc. (2026). *OEIS A400361 revision 17, the second-order Pillai minus floor-gcd conjecture*. URL: <https://oeis.org/A400361>.

*Commentary.*

On the positive real axis this logarithmic derivative of the real Gamma function equals the real restriction of complex digamma. All arguments 1+1/d used below are positive.

**Definition 1.5 (The positive-index coefficient summand).**

$$\forall d \in \operatorname{Nat}\left(\right), \operatorname{b}\left(d\right) = \frac{\operatorname{phi}\left(d\right) \cdot \left(\operatorname{psi}\left(1 + \frac{1}{d}\right) + gamma\right)}{d^{2}}$$

*Formalization.* `D5/S3/ArithSums/A400361SecondTerm.coefficientTerm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ctibor O. Zizka; OEIS Foundation Inc. (2026). *OEIS A400361 revision 17, the second-order Pillai minus floor-gcd conjecture*. URL: <https://oeis.org/A400361>.

*Commentary.*

phi is Euler's totient and gamma is the Euler-Mascheroni constant. For every d>=1, psi(1+1/d)+gamma is the convergent sum over j>=0 of 1/((j+1)*(d*(j+1)+1)). In particular d=1 is included. Each b(d) is nonnegative and at most pi^2/(6*d^2), proving absolute convergence of the defining series.

**Definition 1.6 (The literal second-order constant).**

$$C = \frac{3}{pi^{2}} \cdot \left(\frac{-1}{2} + 2 \cdot gamma - \frac{6 \cdot \operatorname{derivZetaR}\left(2\right)}{pi^{2}}\right) - \frac{pi^{2}}{12} - \frac{1}{2} \cdot \sum_{d \in \operatorname{Ici}\left(1\right)} {\operatorname{b}\left(d\right)}$$

*Formalization.* `D5/S3/ArithSums/A400361SecondTerm.C` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ctibor O. Zizka; OEIS Foundation Inc. (2026). *OEIS A400361 revision 17, the second-order Pillai minus floor-gcd conjecture*. URL: <https://oeis.org/A400361>.

*Commentary.*

The infinite series is over every positive d. It is encoded by d=j+1 for natural j, with no omitted endpoint. The first part is the classical Pillai mean constant; the two remaining parts are the exact limiting mean of the floor-gcd sum.

**Definition 1.7 (The second-order remainder).**

$$\forall N \in \operatorname{Nat}\left(\right), \operatorname{R}\left(N\right) = \operatorname{S}\left(N\right) - \frac{3}{pi^{2}} \cdot N^{2} \cdot \operatorname{log}\left(N\right) - C \cdot N^{2}$$

*Formalization.* `D5/S3/ArithSums/A400361SecondTerm.residual` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ctibor O. Zizka; OEIS Foundation Inc. (2026). *OEIS A400361 revision 17, the second-order Pillai minus floor-gcd conjecture*. URL: <https://oeis.org/A400361>.

*Commentary.*

R is S(N) minus the displayed leading logarithmic term and C*N^2. Division by N^2 tends to zero exactly when R=o(N^2). The equivalence uses that N^2 is nonzero for every positive N.

**Definition 1.8 (The exact unrestricted assertion).**

$$\operatorname{and}\left(\operatorname{Summable}\left(j \mapsto \operatorname{b}\left(j + 1\right)\right), \operatorname{littleOAtTop}\left(N \mapsto \operatorname{R}\left(N\right), N \mapsto N^{2}\right)\right)$$

*Formalization.* `D5/S3/ArithSums/A400361SecondTerm.originalClaim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ctibor O. Zizka; OEIS Foundation Inc. (2026). *OEIS A400361 revision 17, the second-order Pillai minus floor-gcd conjecture*. URL: <https://oeis.org/A400361>.

*Commentary.*

The claim conjoins summability of b(j+1) with R(N)=o(N^2) as N tends to infinity through all natural numbers. There is no subsequence, finite cutoff, arithmetic restriction, or extra hypothesis.

**Theorem 1.9 (The full second-order formula).**

$$\operatorname{and}\left(\operatorname{Summable}\left(j \mapsto \operatorname{b}\left(j + 1\right)\right), \operatorname{littleOAtTop}\left(N \mapsto \operatorname{R}\left(N\right), N \mapsto N^{2}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/A400361SecondTerm.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a400361-second-order-pillai-floor-gcd` (proved) by `D5/S3/ArithSums/A400361SecondTerm.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a400361-second-order-pillai-floor-gcd","declaration_gid":"D5/S3/ArithSums/A400361SecondTerm.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ctibor O. Zizka; OEIS Foundation Inc. (2026). *OEIS A400361 revision 17, the second-order Pillai minus floor-gcd conjecture*. URL: <https://oeis.org/A400361>.

*Commentary.*

Expand gcd by the sum of totients over common divisors. Writing n=d*m and floor(d*m/k)=d*ell gives m=k*ell+r with d*r<k. The edge r=0 contributes the ordinary divisor-sum prefix. For r>0, k=d*r+j gives the positive lattice triangle (d*ell+1)*r+ell*j<=N/d. Its normalized count tends to 1/(2*ell*(d*ell+1)). A summable majorant permits passage through both divisor indices. Consequently the floor-gcd prefix divided by N^2 tends to pi^2/12 plus half the convergent sum of b(d). For the Pillai part, its totient divisor formula gives a Mobius convolution of the weighted divisor pair count. The exact symmetric hyperbola split at floor(sqrt(N)) and the harmonic-number limit give the weighted second term. Dominated convergence transfers it through the Mobius convolution. The quotient-square defect is at most 2/(N*d), and its tail is at most 1/N; multiplication by log(N) therefore leaves a vanishing error. Differentiating the actual zeta-Mobius Dirichlet identity at two supplies the literal zeta derivative. Subtraction yields exactly C and the asserted unrestricted little-o remainder. The classical Pillai asymptotic is prior mathematics, attributed in oeis2026a400361; its formal derivation is used here as a dependency.

## References

- Truth anchor: `D5/S3/ArithSums/A400361SecondTerm.C`
- Truth anchor: `D5/S3/ArithSums/A400361SecondTerm.S`
- Truth anchor: `D5/S3/ArithSums/A400361SecondTerm.a`
- Truth anchor: `D5/S3/ArithSums/A400361SecondTerm.coefficientTerm`
- Truth anchor: `D5/S3/ArithSums/A400361SecondTerm.floorGcd`
- Truth anchor: `D5/S3/ArithSums/A400361SecondTerm.originalClaim`
- Truth anchor: `D5/S3/ArithSums/A400361SecondTerm.realDigamma`
- Truth anchor: `D5/S3/ArithSums/A400361SecondTerm.residual`
- Truth anchor: `D5/S3/ArithSums/A400361SecondTerm.result`
- Dependency: [D5/S3/ArithSums/A400361PillaiMean](A400361PillaiMean.md)
