# Prime Symbol Mean Square

## Abstract

SOURCE_ONLY_UNCOMPILED: author exposition; no kernel, emission or Reg acceptance claim.

All descriptions accompany the canonical-path T2 source candidate; its retained signatures, definitions and proofs preserve the pinned bytes. SOURCE_ONLY_UNCOMPILED: Lean elaboration, kernel acceptance, sorry and axiom-closure checks, scoped reports, Scribe emission, Reg, required CI and delivery remain unverified. Utility:none describes parameterized symbolic definitions, identities and estimates, including private helpers; none delivers a bounded enumeration, checker/reflection infrastructure, numerical-certificate reduction or certified fixed instance. Other utility fields are not-applicable(kind=none). No RH, Robin inequality or physical-positivity conclusion is claimed. Throughout, c,q are natural, m and block start M are integers unless a tail specifies natural M>0. Write I(c)=[2,c), a(q)=primeWeight(q)=vonMangoldt(q)/sqrt(q), L=log(c), z(c,q)=primePhase(c,q), S(c,m)=primeSymbol(c,m), D(c)=primeSquareMass(c), C(c)=primeCross(c), and B(c,M)=primeTailBudget(c,M). These display abbreviations are not new Lean declarations. The finite cutoff retains every integer and therefore every prime power. Each item also records its exact pinned signature or definition to fix all quantifiers and casts.

**Definition 1.1 (Every integer below the cutoff).**

$$\operatorname{I}(c)=\operatorname{Ico}(2, c)$$

*Formalization.* `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.primeIndices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural c, I(c)=Finset.Ico 2 c. This is an interval of integers, not a set restricted to primes. Since a(q)=vonMangoldt(q)/sqrt(q), all supported higher prime powers remain in every subsequent sum; indices with zero von Mangoldt weight contribute zero.

Exact pinned definition (source only): def primeIndices (c : ℕ) : Finset ℕ := Finset.Ico 2 c

**Definition 1.2 (The actual logarithmic angle).**

$$\operatorname{theta}(c, q)=\operatorname{div}(\operatorname{log}(q), \operatorname{logLength}(c))$$

*Formalization.* `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.theta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural c,q, theta(c,q)=log(q)/log(c). Lean division and logarithms are total; the strict geometric assertions below require c>=2 and q in I(c). No spacing or irrationality hypothesis is added.

Exact pinned definition (source only): def theta (c q : ℕ) : ℝ := Real.log (q : ℝ) / logLength c

**Definition 1.3 (The unit-circle phase).**

$$\operatorname{z}(c, q)=\operatorname{circleMap}(0, 1, 2 pi \operatorname{theta}(c, q))$$

*Formalization.* `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.primePhase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For all natural c,q, z(c,q)=circleMap 0 1 (2*pi*theta(c,q)), equivalently exp(2*pi*i*theta(c,q)). Integer powers of this phase give the sine at every signed lattice mode.

Exact pinned definition (source only): def primePhase (c q : ℕ) : ℂ := circleMap 0 1 (2 * Real.pi * theta c q)

**Definition 1.4 (The complete finite sine symbol).**

$$\operatorname{S}(c, m)=\operatorname{WeightedSineSum}(c, m)$$

*Formalization.* `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.primeSymbol` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural c and integer m, WeightedSineSum(c,m)=sum_{q in I(c)} a(q)*sin(2*pi*m*theta(c,q)). This is primeSymbol, with the positive sine sign; the owner arithmeticBoundarySymbol contains its negative. Every prime power below c is retained.

Exact pinned definition (source only): def primeSymbol (c : ℕ) (m : ℤ) : ℝ :=   ∑ q ∈ primeIndices c, primeWeight q * Real.sin (2 * Real.pi * (m : ℝ) * theta c q)

**Definition 1.5 (The full diagonal square mass).**

$$\operatorname{D}(c)=\operatorname{PrimeWeightSquareSum}(c)$$

*Formalization.* `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.primeSquareMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural c, D(c)=sum_{q in I(c)} a(q)^2. In particular it includes squares of the weights at higher prime powers. The notation D here denotes primeSquareMass, not the generic real D in the Abel lemma.

Exact pinned definition (source only): def primeSquareMass (c : ℕ) : ℝ := ∑ q ∈ primeIndices c, primeWeight q ^ 2

**Definition 1.6 (Ordered unequal-pair geometric error).**

$$\operatorname{orderedCross}(s, a, z)=\operatorname{OrderedUnequalPairSum}(s, a, z)$$

*Formalization.* `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.orderedCross` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any finite natural set s, real a:N->R and complex z:N->C, this is sum_{p in s} sum_{q in s} (if p=q then 0 else 2*abs(a(p)*a(q))/norm(1-z(p)*conj(z(q)))). Each unordered unequal pair occurs twice, and the factor 2 is paid for each ordered pair. This definition itself assumes neither unit norms nor noncollision.

Exact pinned definition (source only): def orderedCross (s : Finset ℕ) (a : ℕ → ℝ) (z : ℕ → ℂ) : ℝ :=   ∑ p ∈ s, ∑ q ∈ s,     if p = q then 0 else 2 * |a p * a q| / ‖1 - z p * conj (z q)‖

**Definition 1.7 (The actual phase cross constant).**

$$\operatorname{C}(c)=\operatorname{orderedCross}(\operatorname{I}(c), primeWeight, \operatorname{primePhase}(c))$$

*Formalization.* `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.primeCross` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural c, C(c)=orderedCross(I(c),primeWeight,primePhase(c)). The actual unit phases and logarithmic noncollision theorem justify geometric denominator use when c>=2. There is no imposed spacing constant or removed prime power.

Exact pinned definition (source only): def primeCross (c : ℕ) : ℝ := orderedCross (primeIndices c) primeWeight (primePhase c)

**Theorem 1.8 (Positive logarithmic length).**

$$\operatorname{AtLeastTwo}(c)\Rightarrow\operatorname{Positive}(\operatorname{logLength}(c))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.logLength_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural c>=2, logLength(c)=log(c)>0. This supplies the positive denominator in the actual angle comparisons.

Exact pinned declaration signature (source only): theorem logLength_pos {c : ℕ} (hc : 2 ≤ c) : 0 < logLength c

**Theorem 1.9 (Every included angle lies in the open unit interval).**

$$\operatorname{AtLeastTwo}(c)\land\operatorname{Member}(q, \operatorname{I}(c))\Rightarrow\operatorname{Positive}(\operatorname{theta}(c, q))\land\operatorname{LessThanOne}(\operatorname{theta}(c, q))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.phase_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>=2 and q in I(c), 0<theta(c,q)<1, since 2<=q<c and logarithm is strictly increasing on positive reals. At c=2 the membership hypothesis is empty.

Exact pinned declaration signature (source only): theorem phase_geometry {c q : ℕ} (hc : 2 ≤ c) (hq : q ∈ primeIndices c) :     0 < theta c q ∧ theta c q < 1

**Theorem 1.10 (Unit norm without a cutoff hypothesis).**

$$\operatorname{norm}(\operatorname{z}(c, q))=1$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.primePhase_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural c,q, norm(z(c,q))=1. No c>=2 or interval-membership premise is required for this circleMap identity.

Exact pinned declaration signature (source only): theorem primePhase_norm (c q : ℕ) : ‖primePhase c q‖ = 1

**Theorem 1.11 (Difference noncollision from the actual logarithms).**

$$\operatorname{AtLeastTwo}(c)\land\operatorname{Member}(p, \operatorname{I}(c))\land\operatorname{Member}(q, \operatorname{I}(c))\land\operatorname{Distinct}(p, q)\Rightarrow\operatorname{NotEqualOne}(\operatorname{z}(c, p) \operatorname{conj}(\operatorname{z}(c, q)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.primePhase_noncollision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>=2, p,q in I(c) and p!=q, z(c,p)*conj(z(c,q))!=1. The proof bounds the logarithmic difference strictly inside one period, then uses injectivity of log on positive reals. It requires no separate spacing, irrationality or equidistribution premise.

Exact pinned declaration signature (source only): theorem primePhase_noncollision {c p q : ℕ} (hc : 2 ≤ c)     (hp : p ∈ primeIndices c) (hq : q ∈ primeIndices c) (hpq : p ≠ q) :     primePhase c p * conj (primePhase c q) ≠ 1

**Theorem 1.12 (The upper-endpoint sine vanishes).**

$$\operatorname{AtLeastTwo}(c)\Rightarrow\operatorname{OwnerPrimeTerm}(c, c, m)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.owner_term_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>=2 and any integer m, a(c)*sin(frequency(c,m)*log(c))=0, because the angle is 2*pi*m. This permits the inclusive endpoint without deleting a nonzero contribution.

Exact pinned declaration signature (source only): theorem owner_term_cutoff {c : ℕ} (hc : 2 ≤ c) (m : ℤ) :     primeWeight c * Real.sin (frequency c m * Real.log (c : ℝ)) = 0

**Theorem 1.13 (Exact identification of the native range sum).**

$$\operatorname{OwnerPrimeRangeSum}(c, m)=\operatorname{S}(c, m)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.owner_prime_sum_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural c and integer m, sum_{q in Finset.range c} a(q)*sin(frequency(c,m)*log(q))=S(c,m). The q=0 and q=1 terms vanish; frequency(c,m)*log(q)=2*pi*m*theta(c,q). This identity has no c>=2 premise and identifies the owner prime component with its exact sign.

Exact pinned declaration signature (source only): theorem owner_prime_sum_eq (c : ℕ) (m : ℤ) :     (∑ q ∈ Finset.range c, primeWeight q * Real.sin (frequency c m * Real.log (q : ℝ))) =       primeSymbol c m

**Theorem 1.14 (The inclusive cutoff is the same symbol).**

$$\operatorname{AtLeastTwo}(c)\Rightarrow\operatorname{OwnerPrimeInclusiveSum}(c, m)=\operatorname{S}(c, m)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.owner_prime_sum_inclusive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>=2 and any integer m, sum_{q in range(c+1)} a(q)*sin(frequency(c,m)*log(q))=S(c,m). It consumes owner_term_cutoff and owner_prime_sum_eq, with the upper term explicitly accounted for.

Exact pinned declaration signature (source only): theorem owner_prime_sum_inclusive {c : ℕ} (hc : 2 ≤ c) (m : ℤ) :     (∑ q ∈ Finset.range (c + 1), primeWeight q * Real.sin (frequency c m * Real.log (q : ℝ))) =       primeSymbol c m

**Theorem 1.15 (Exact complex exponential representation).**

$$\operatorname{S}(c, m)=\operatorname{im}(\operatorname{E}(c, m))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.primeSymbol_is_im` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural c and integer m, E(c,m)=sum_{q in I(c)} (a(q):C)*z(c,q)^m and S(c,m)=Im(E(c,m)). The exponent is an integer, so negative and zero modes are retained.

Exact pinned declaration signature (source only): theorem primeSymbol_is_im (c : ℕ) (m : ℤ) :     primeSymbol c m =       (∑ q ∈ primeIndices c, (primeWeight q : ℂ) * primePhase c q ^ m).im

**Theorem 1.16 (The single geometric-series estimate).**

$$\operatorname{UnitNorm}(z)\land\operatorname{NotEqualOne}(z)\Rightarrow\operatorname{norm}(\operatorname{GeometricBlock}(z, M, K))\leq\operatorname{div}(2, \operatorname{norm}(1-z))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.geometric_block_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary complex z with norm(z)=1 and z!=1, integer M and natural K, norm(sum_{j<K} z^(M+j))<=2/norm(1-z). This includes K=0 and every signed start. It uses the existing finite geometric-sum formula, with no asymptotic averaging argument.

Exact pinned declaration signature (source only): theorem geometric_block_norm {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1)     (M : ℤ) (K : ℕ) :     ‖∑ j ∈ Finset.range K, z ^ (M + (j : ℤ))‖ ≤ 2 / ‖1 - z‖

**Theorem 1.17 (The full ordered complex norm-square expansion).**

$$\operatorname{normSq}(\operatorname{E}(s, a, z, m))=\operatorname{OrderedConjugatePairSum}(s, a, z, m)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.norm_square_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite natural s, real coefficients a, arbitrary complex phases z and integer m, E(s,a,z,m)=sum_{p in s}(a(p):C)*z(p)^m. Its squared norm equals sum_{p in s}sum_{q in s} Re(((a(p)*a(q):R):C)*(z(p)*conj(z(q)))^m). Unit norm and noncollision are not hypotheses of this algebraic identity; the ordered complex summands are not assumed symmetric.

Exact pinned declaration signature (source only): theorem norm_square_expansion (s : Finset ℕ) (a : ℕ → ℝ) (z : ℕ → ℂ) (m : ℤ) :     ‖∑ p ∈ s, (a p : ℂ) * z p ^ m‖ ^ 2 =       ∑ p ∈ s, ∑ q ∈ s, (((a p * a q : ℝ) : ℂ) * (z p * conj (z q)) ^ m).re

**Theorem 1.18 (Uniform finite blocks with every prime power).**

$$\operatorname{AtLeastTwo}(c)\Rightarrow\operatorname{SquareBlock}(c, M, K)\leq K \operatorname{D}(c)+\operatorname{C}(c)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.prime_symbol_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>=2, any integer M and any natural K, SquareBlock(c,M,K)=sum_{j<K} S(c,M+j)^2 <= K*D(c)+C(c). The proof bounds the imaginary square by the complex norm square and applies geometric_block_norm to ordered unequal pairs. K=0 and negative block starts are admitted.

Exact pinned declaration signature (source only): theorem prime_symbol_block {c : ℕ} (hc : 2 ≤ c) (M : ℤ) (K : ℕ) :     (∑ j ∈ Finset.range K, primeSymbol c (M + (j : ℤ)) ^ 2) ≤       (K : ℝ) * primeSquareMass c + primeCross c

**Theorem 1.19 (Discrete Abel majorization with exact hypotheses).**

$$\operatorname{AbelHypotheses}(x, w, D, C)\Rightarrow\operatorname{WeightedPartialSum}(x, w, K)\leq D \operatorname{WeightPartialSum}(w, K)+C \operatorname{AtZero}(w)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.finite_abel_majorant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x,w:N->R and D,C:R, assume 0<=C, every w(i)>=0, w(i+1)<=w(i), and for every natural k, sum_{i<k}x(i)<=k*D+C. Then for every natural K, sum_{i<K}x(i)*w(i)<=D*sum_{i<K}w(i)+C*w(0). No sign hypothesis is imposed on x or D. The proof uses Mathlib finite summation by parts and retains its finite boundary contribution, including K=0.

Exact pinned declaration signature (source only): theorem finite_abel_majorant (x w : ℕ → ℝ) (D C : ℝ)     (hC : 0 ≤ C) (hw : ∀ i, 0 ≤ w i) (hanti : ∀ i, w (i + 1) ≤ w i)     (hA : ∀ K, (∑ i ∈ Finset.range K, x i) ≤ (K : ℝ) * D + C) (K : ℕ) :     (∑ i ∈ Finset.range K, x i * w i) ≤       D * (∑ i ∈ Finset.range K, w i) + C * w 0

**Definition 1.20 (The actual positive-tail enumeration weight).**

$$\operatorname{W}(M, j)=\operatorname{square}(\operatorname{inv}(M+j+1))$$

*Formalization.* `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.inverseSquareWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural M,j, W(M,j)=((M:R)+(j:R)+1)^(-2), written in Lean as the square of the inverse. The enumeration m=M+j+1 visits each positive mode above M exactly once.

Exact pinned definition (source only): def inverseSquareWeight (M j : ℕ) : ℝ := (((M : ℝ) + (j : ℝ) + 1)⁻¹) ^ 2

**Definition 1.21 (The unrefined prime tail budget).**

$$\operatorname{B}(c, M)=\operatorname{div}(\operatorname{D}(c), M)+\operatorname{div}(\operatorname{C}(c), \operatorname{square}(M+1))$$

*Formalization.* `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.primeTailBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural c,M, B(c,M)=D(c)/M+C(c)/(M+1)^2. This is primeTailBudget; the convergent-tail estimates below require c>=2 and M>0. The first term uses the inverse-square partial-sum bound 1/M.

Exact pinned definition (source only): def primeTailBudget (c M : ℕ) : ℝ :=   primeSquareMass c / (M : ℝ) + primeCross c / ((M : ℝ) + 1) ^ 2

**Theorem 1.22 (Antitonicity of the sampled inverse square).**

$$\operatorname{Positive}(M)\Rightarrow\operatorname{W}(M, j+1)\leq\operatorname{W}(M, j)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.inverseSquareWeight_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural M>0 and every natural j, inverseSquareWeight(M,j+1)<=inverseSquareWeight(M,j). This is the exact weight monotonicity supplied to finite_abel_majorant.

Exact pinned declaration signature (source only): theorem inverseSquareWeight_antitone {M : ℕ} (hM : 0 < M) (i : ℕ) :     inverseSquareWeight M (i + 1) ≤ inverseSquareWeight M i

**Theorem 1.23 (Summability before the actual prime-square tsum bound).**

$$\operatorname{AtLeastTwo}(c)\land\operatorname{Positive}(M)\Rightarrow\operatorname{Summable}(\operatorname{PrimeEnergySequence}(c, M))\land\operatorname{PrimeEnergyTsum}(c, M)\leq\operatorname{B}(c, M)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.prime_symbol_square_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>=2 and M>0, the nonnegative sequence j |-> S(c,M+j+1)^2*W(M,j) is summable, and its actual tsum is <=B(c,M). Uniformly bounded partial sums establish summability first; a totalized divergent tsum is not used. Every m>M is present.

Exact pinned declaration signature (source only): theorem prime_symbol_square_tail {c M : ℕ} (hc : 2 ≤ c) (hM : 0 < M) :     Summable (fun j : ℕ =>       primeSymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight M j) ∧     (∑' j : ℕ, primeSymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight M j) ≤       primeTailBudget c M

**Theorem 1.24 (Exact complex scaling of the energy).**

$$\operatorname{ComplexEnergy}(c, M, j, beta)=\operatorname{normSq}(beta) \operatorname{square}(\operatorname{S}(c, M+j+1)) \operatorname{W}(M, j)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.complex_prime_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural c,M,j and arbitrary complex beta, norm(beta*(S(c,M+j+1):C)/(M+j+1:C))^2=norm(beta)^2*(S(c,M+j+1)^2*W(M,j)). There are no c>=2, M>0, reality or cancellation premises for this exact identity.

Exact pinned declaration signature (source only): theorem complex_prime_energy (c M j : ℕ) (β : ℂ) :     ‖β * (primeSymbol c ((M + j + 1 : ℕ) : ℤ) : ℂ) / ((M + j + 1 : ℕ) : ℂ)‖ ^ 2 =       ‖β‖ ^ 2 * (primeSymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight M j)

**Theorem 1.25 (An actual tail for arbitrary complex beta).**

$$\operatorname{AtLeastTwo}(c)\land\operatorname{Positive}(M)\Rightarrow\operatorname{Summable}(\operatorname{ComplexPrimeEnergySequence}(c, M, beta))\land\operatorname{ComplexPrimeEnergyTsum}(c, M, beta)\leq\operatorname{normSq}(beta) \operatorname{B}(c, M)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.complex_prime_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>=2, M>0 and any beta:C, j |-> norm(beta*S(c,M+j+1)/(M+j+1))^2 is summable and its tsum is <=norm(beta)^2*(D(c)/M+C(c)/(M+1)^2). The coefficient remains arbitrary complex and its exact squared norm is retained.

Exact pinned declaration signature (source only): theorem complex_prime_tail {c M : ℕ} (hc : 2 ≤ c) (hM : 0 < M) (β : ℂ) :     Summable (fun j : ℕ =>       ‖β * (primeSymbol c ((M + j + 1 : ℕ) : ℤ) : ℂ) / ((M + j + 1 : ℕ) : ℂ)‖ ^ 2) ∧     (∑' j : ℕ,       ‖β * (primeSymbol c ((M + j + 1 : ℕ) : ℤ) : ℂ) / ((M + j + 1 : ℕ) : ℂ)‖ ^ 2) ≤         ‖β‖ ^ 2 * (primeSquareMass c / (M : ℝ) + primeCross c / ((M : ℝ) + 1) ^ 2)

**Definition 1.26 (The complete retained complex boundary moment).**

$$\operatorname{Moment}(c, S, A, v, j)=\operatorname{WeightedBoundaryMomentSum}(c, S, A, v, j)$$

*Formalization.* `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.retainedBoundaryMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural c,j, finite S subset N, A:N->R and v:N->C, Moment(c,S,A,v,j)=sum_{n in S}(-1)^n*(A(n):C)*v(n)*(frequency(c,(n:Z)):C)^(2*j). The amplitudes, phases, arbitrary complex coefficients and owner frequency are all retained.

Exact pinned definition (source only): def retainedBoundaryMoment (c : ℕ) (S : Finset ℕ) (A : ℕ → ℝ)     (v : ℕ → ℂ) (j : ℕ) : ℂ :=   ∑ n ∈ S, (-1 : ℂ) ^ n * (A n : ℂ) * v n *     (frequency c (n : ℤ) : ℂ) ^ (2 * j)

**Definition 1.27 (The finite sum of actual prime-symbol columns).**

$$\operatorname{RetainedColumn}(c, S, A, v, j, kappa, m)=\operatorname{PrimeColumnSum}(c, S, A, v, j, kappa, m)$$

*Formalization.* `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.retainedArithmeticColumn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural c,j,m, finite S subset N, real A, complex v and arbitrary kappa:C, the column is sum_{n in S} kappa*((-1)^n*(A(n):C)*v(n)*(frequency(c,n):C)^(2*j))*(S(c,m):C)/(m:C). Here S(c,m) denotes the prime sine symbol, while the set S is the finite index set. Kappa is explicit normalization supplied by the caller.

Exact pinned definition (source only): def retainedArithmeticColumn (c : ℕ) (S : Finset ℕ) (A : ℕ → ℝ)     (v : ℕ → ℂ) (j : ℕ) (κ : ℂ) (m : ℕ) : ℂ :=   ∑ n ∈ S, κ * ((-1 : ℂ) ^ n * (A n : ℂ) * v n *     (frequency c (n : ℤ) : ℂ) ^ (2 * j)) * (primeSymbol c (m : ℤ) : ℂ) / (m : ℂ)

**Theorem 1.28 (The retained moment controls its genuine infinite tail).**

$$\operatorname{AtLeastTwo}(c)\land\operatorname{Positive}(M)\Rightarrow\operatorname{Summable}(\operatorname{RetainedColumnEnergySequence}(c, M, S, A, v, j, kappa))\land\operatorname{RetainedColumnEnergyTsum}(c, M, S, A, v, j, kappa)\leq\operatorname{normSq}(kappa) \operatorname{normSq}(\operatorname{Moment}(c, S, A, v, j)) \operatorname{B}(c, M)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.retained_arithmetic_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>=2, M>0 and every finite S subset N, A:N->R, v:N->C, natural j and kappa:C, the column energy at m=M+k+1 is summable in k. Its tsum is <=norm(kappa)^2*norm(Moment(c,S,A,v,j))^2*B(c,M). The finite sum is collected algebraically before applying complex_prime_tail. No moment is set to zero and no reality assumption is imposed on v or kappa.

Exact pinned declaration signature (source only): theorem retained_arithmetic_tail {c M : ℕ} (hc : 2 ≤ c) (hM : 0 < M)     (S : Finset ℕ) (A : ℕ → ℝ) (v : ℕ → ℂ) (j : ℕ) (κ : ℂ) :     Summable (fun k : ℕ => ‖retainedArithmeticColumn c S A v j κ (M + k + 1)‖ ^ 2) ∧     (∑' k : ℕ, ‖retainedArithmeticColumn c S A v j κ (M + k + 1)‖ ^ 2) ≤       ‖κ‖ ^ 2 * ‖retainedBoundaryMoment c S A v j‖ ^ 2 *         (primeSquareMass c / (M : ℝ) + primeCross c / ((M : ℝ) + 1) ^ 2)

**Definition 1.29 (The canonical positive-sign prime far term).**

$$\operatorname{PrimeFar}(c, S, v, m)=\operatorname{div}(\operatorname{S}(c, m) \operatorname{CoefficientSum}(S, v), pi m)$$

*Formalization.* `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.canonicalPrimeFirstJetFar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural c, finite S subset Z, v:Z->C and any integer m, PrimeFar(c,S,v,m)=(primeSymbol(c,m):C)*sum_{n in S}v(n)/((pi:C)*(m:C)). The positive sign follows from subtracting the exterior arithmetic symbol, whose prime component is negative. The exact pi normalization is preserved.

Exact pinned definition (source only): def canonicalPrimeFirstJetFar (c : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) (m : ℤ) : ℂ :=   (primeSymbol c m : ℂ) * (∑ n ∈ S, v n) / ((Real.pi : ℂ) * (m : ℂ))

**Theorem 1.30 (An exact split of the existing first jet).**

$$\operatorname{couplingFirstJet}(c, S, v, m)=\operatorname{div}(\operatorname{InteriorSymbolMoment}(c, S, v), pi m)-\operatorname{div}({\operatorname{arithmeticBoundarySymbol}(c, m)+\operatorname{S}(c, m)} \operatorname{CoefficientSum}(S, v), pi m)+\operatorname{PrimeFar}(c, S, v, m)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.canonical_first_jet_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural c, finite integer S, arbitrary complex v and integer m, Jet(c,S,v,m)=alpha/(pi*m)-(arithmeticBoundarySymbol(c,m)+primeSymbol(c,m))*beta/(pi*m)+PrimeFar(c,S,v,m), where alpha=sum_{n in S}(arithmeticBoundarySymbol(c,n):C)*v(n) and beta=sum_{n in S}v(n). All real symbols are cast to C. This is an exact totalized-division identity, with no exterior or nonzero-mode hypothesis. The interior full symbol and exterior nonprime component remain present; it does not assert the separate full-symbol physical bridge.

Exact pinned declaration signature (source only): theorem canonical_first_jet_split (c : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) (m : ℤ) :     couplingFirstJet c S v m =       (∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * v n) /         ((Real.pi : ℂ) * (m : ℂ)) -       ((arithmeticBoundarySymbol c m + primeSymbol c m : ℝ) : ℂ) *         (∑ n ∈ S, v n) / ((Real.pi : ℂ) * (m : ℂ)) +       canonicalPrimeFirstJetFar c S v m

**Theorem 1.31 (The exact pi-normalized first-jet prime tail).**

$$\operatorname{AtLeastTwo}(c)\land\operatorname{Positive}(M)\Rightarrow\operatorname{Summable}(\operatorname{PrimeFarEnergySequence}(c, M, S, v))\land\operatorname{PrimeFarEnergyTsum}(c, M, S, v)\leq\operatorname{div}(\operatorname{normSq}(\operatorname{CoefficientSum}(S, v)), \operatorname{square}(pi)) \operatorname{B}(c, M)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.canonical_first_jet_prime_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>=2, M>0, every finite S subset Z and arbitrary complex v, j |-> norm(PrimeFar(c,S,v,M+j+1))^2 is summable. Its tsum is <=(norm(sum_{n in S}v(n))^2/pi^2)*(D(c)/M+C(c)/(M+1)^2). This is the actual existing first-jet prime term with its pi^(-2) factor; the nonprime component and column remainder remain separate.

Exact pinned declaration signature (source only): theorem canonical_first_jet_prime_tail {c M : ℕ} (hc : 2 ≤ c) (hM : 0 < M)     (S : Finset ℤ) (v : ℤ → ℂ) :     Summable (fun k : ℕ => ‖canonicalPrimeFirstJetFar c S v ((M + k + 1 : ℕ) : ℤ)‖ ^ 2) ∧     (∑' k : ℕ, ‖canonicalPrimeFirstJetFar c S v ((M + k + 1 : ℕ) : ℤ)‖ ^ 2) ≤       (‖∑ n ∈ S, v n‖ ^ 2 / Real.pi ^ 2) *         (primeSquareMass c / (M : ℝ) + primeCross c / ((M : ℝ) + 1) ^ 2)

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.canonicalPrimeFirstJetFar`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.canonical_first_jet_prime_tail`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.canonical_first_jet_split`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.complex_prime_energy`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.complex_prime_tail`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.finite_abel_majorant`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.geometric_block_norm`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.inverseSquareWeight`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.inverseSquareWeight_antitone`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.logLength_pos`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.norm_square_expansion`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.orderedCross`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.owner_prime_sum_eq`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.owner_prime_sum_inclusive`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.owner_term_cutoff`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.phase_geometry`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.primeCross`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.primeIndices`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.primePhase`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.primePhase_noncollision`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.primePhase_norm`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.primeSquareMass`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.primeSymbol`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.primeSymbol_is_im`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.primeTailBudget`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.prime_symbol_block`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.prime_symbol_square_tail`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.retainedArithmeticColumn`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.retainedBoundaryMoment`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.retained_arithmetic_tail`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare.theta`
- Dependency: [D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet](WeilArithmeticCouplingJet.md)
- Dependency: [D5/S3/Weil/ZetaBridge/WeilInfiniteComplementLeakage](WeilInfiniteComplementLeakage.md)
