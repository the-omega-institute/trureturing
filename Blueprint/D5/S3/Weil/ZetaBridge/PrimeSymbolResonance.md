# Prime Symbol Resonance

## Abstract

SOURCE_ONLY_UNCOMPILED: exact resonance source exposition; no validation claim.

All entries accompany the canonical-path T3 source candidate; every surviving signature, definition and proof, including private tail_partial, preserves the pinned bytes. SOURCE_ONLY_UNCOMPILED: Lean elaboration, kernel acceptance, sorry and axiom-closure checks, scoped reports, Scribe emission, Reg, required CI and delivery remain unverified. Utility:none describes parameterized finite-sum definitions, resonance and convolution/support classification, geometric estimates and convergent tails, including private helpers; none delivers a bounded enumeration, checker/reflection infrastructure, numerical-certificate reduction or certified fixed instance. Other utility fields are not-applicable(kind=none). Write I(c)=[2,c), a(q)=primeWeight(q)=Lambda(q)/sqrt(q), z(c,q)=T2.primePhase(c,q), S(c,m)=T2.primeSymbol(c,m), D(c)=T2.primeSquareMass(c), Cdiff(c)=T2.primeCross(c), R(c)=resonantMass(c), Csum(c)=sumCross(c), mu(c)=mean(c), O(c)=offset(c), B3(c,N)=tailBudget(c,N). LambdaConvolution(c) means the actual ArithmeticFunction Dirichlet product (Lambda*Lambda)(c). These are display abbreviations, not additional Lean declarations. The finite sums retain every prime power; ordered pairs and resonant self-pairs are counted exactly. Exact source signatures below fix all hypotheses and casts.

**Definition 1.1 (Ordered sum-resonant mass, including self-pairs).**

$$\operatorname{R}(c)=\operatorname{OrderedResonantWeightSum}(c)$$

*Formalization.* `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.resonantMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural c, R(c)=sum_{p in I(c)}sum_{q in I(c)} (if p*q=c then a(p)*a(q) else 0). Pairs are ordered, so p!=q appears in both orders; p=q is retained when p^2=c. The indices p,q are integers in [2,c), not necessarily primes: von Mangoldt supports every prime power. For example c=4 retains (2,2), while c=12 retains the supported ordered pairs (3,4) and (4,3).

Exact pinned definition (source only): def resonantMass (c : ℕ) : ℝ :=   ∑ p ∈ primeIndices c, ∑ q ∈ primeIndices c,     if p * q = c then primeWeight p * primeWeight q else 0

**Definition 1.2 (The full nonresonant sum-angle error).**

$$\operatorname{Csum}(c)=\operatorname{OrderedNonresonantSumChannel}(c)$$

*Formalization.* `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.sumCross` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural c, Csum(c)=sum_{p in I(c)}sum_{q in I(c)} (if p*q=c then 0 else 2*abs(a(p)*a(q))/norm(1-z(c,p)*z(c,q))). This is the unconjugated phase product. The factor 2 is per ordered pair, and a diagonal p=q remains whenever p^2!=c. Only genuinely resonant products p*q=c are excluded from these geometric denominators.

Exact pinned definition (source only): def sumCross (c : ℕ) : ℝ :=   ∑ p ∈ primeIndices c, ∑ q ∈ primeIndices c,     if p * q = c then 0 else       2 * |primeWeight p * primeWeight q| / ‖1 - primePhase c p * primePhase c q‖

**Definition 1.3 (The exact resonance-corrected mean).**

$$\operatorname{mu}(c)=\operatorname{div}(\operatorname{D}(c)-\operatorname{R}(c), 2)$$

*Formalization.* `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.mean` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural c, mu(c)=(D(c)-R(c))/2. The resonant subtraction is essential, including prime-power factors and resonant self-pairs. Nonnegativity for c>=2 is derived later from actual nonnegative finite sine-square blocks; it is not inserted as a premise.

Exact pinned definition (source only): def mean (c : ℕ) : ℝ := (primeSquareMass c - resonantMass c) / 2

**Definition 1.4 (Both geometric channels with the exact half factor).**

$$\operatorname{O}(c)=\operatorname{div}(\operatorname{Cdiff}(c)+\operatorname{Csum}(c), 2)$$

*Formalization.* `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.offset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural c, O(c)=(primeCross(c)+sumCross(c))/2. Cdiff denotes the T2 ordered unequal-pair conjugated channel. Csum denotes the T3 nonresonant unconjugated channel. Each channel retains its per-pair factor 2 before their sum is divided by 2.

Exact pinned definition (source only): def offset (c : ℕ) : ℝ := (primeCross c + sumCross c) / 2

**Definition 1.5 (The refined infinite-tail budget).**

$$\operatorname{B3}(c, N)=\operatorname{div}(\operatorname{mu}(c), N)+\operatorname{div}(\operatorname{O}(c), \operatorname{square}(N+1))$$

*Formalization.* `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.tailBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural c,N, B3(c,N)=mu(c)/N+O(c)/(N+1)^2. This is exactly tailBudget. Tail theorems below use c>=2 and N>0, preserving both denominators and the resonance-corrected leading constant.

Exact pinned definition (source only): def tailBudget (c N : ℕ) : ℝ :=   mean c / (N : ℝ) + offset c / ((N : ℝ) + 1) ^ 2

**Theorem 1.6 (Difference resonance occurs exactly on the diagonal).**

$$\operatorname{AtLeastTwo}(c)\land\operatorname{Member}(p, \operatorname{I}(c))\land\operatorname{Member}(q, \operatorname{I}(c))\Rightarrow\operatorname{Equivalent}(\operatorname{z}(c, p) \operatorname{conj}(\operatorname{z}(c, q))=1, p=q)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.difference_resonance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>=2 and p,q in I(c), z(c,p)*conj(z(c,q))=1 iff p=q. The forward implication consumes T2 actual-log noncollision, and the reverse implication uses unit norm. This is the conjugated difference channel, without any added phase-spacing hypothesis.

Exact pinned declaration signature (source only): theorem difference_resonance {c p q : ℕ} (hc : 2 ≤ c)     (hp : p ∈ primeIndices c) (hq : q ∈ primeIndices c) :     primePhase c p * conj (primePhase c q) = 1 ↔ p = q

**Theorem 1.7 (Sum resonance occurs exactly when the product is the cutoff).**

$$\operatorname{AtLeastTwo}(c)\land\operatorname{Member}(p, \operatorname{I}(c))\land\operatorname{Member}(q, \operatorname{I}(c))\Rightarrow\operatorname{Equivalent}(\operatorname{z}(c, p) \operatorname{z}(c, q)=1, p q=c)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.sum_resonance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>=2 and p,q in I(c), z(c,p)*z(c,q)=1 iff p*q=c. Each theta lies in (0,1), so the sum angle is in (0,4*pi); its only circle identity occurs at 2*pi. Thus log(p)+log(q)=log(c), and positivity plus log injectivity gives p*q=c. Both orders and the p=q possibility are kept. No irrationality, generic position or equidistribution premise occurs.

Exact pinned declaration signature (source only): theorem sum_resonance {c p q : ℕ} (hc : 2 ≤ c)     (hp : p ∈ primeIndices c) (hq : q ∈ primeIndices c) :     primePhase c p * primePhase c q = 1 ↔ p * q = c

**Theorem 1.8 (Every finite block has the exact corrected mean).**

$$\operatorname{AtLeastTwo}(c)\Rightarrow\operatorname{abs}(\operatorname{SquareBlock}(c, M, K)-K \operatorname{mu}(c))\leq\operatorname{O}(c)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.prime_symbol_exact_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>=2, any integer M and natural K, abs(sum_{j<K}S(c,M+j)^2-K*mu(c))<=O(c). The source combines the norm-square and unconjugated-square expansions via 2*(Im E)^2=norm(E)^2-Re(E^2). The two exact resonance classifications supply D and R; the centered geometric estimates supply Cdiff and Csum. K=0, negative starts, all prime powers and resonant self-pairs are included.

Exact pinned declaration signature (source only): theorem prime_symbol_exact_block {c : ℕ} (hc : 2 ≤ c) (M : ℤ) (K : ℕ) :     |(∑ j ∈ Finset.range K, primeSymbol c (M + (j : ℤ)) ^ 2) -       (K : ℝ) * mean c| ≤ offset c

**Theorem 1.9 (Nonnegative offset at every cutoff).**

$$0\leq\operatorname{O}(c)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.offset_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural c, 0<=offset(c). Both finite channel sums have nonnegative terms, including totalized divisions. This statement has no c>=2 hypothesis.

Exact pinned declaration signature (source only): theorem offset_nonneg (c : ℕ) : 0 ≤ offset c

**Theorem 1.10 (Nonnegative mean derived from finite blocks).**

$$\operatorname{AtLeastTwo}(c)\Rightarrow0\leq\operatorname{mu}(c)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.mean_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>=2, 0<=mean(c). If mean were negative, an integer block length large enough to dominate the fixed offset would contradict the nonnegativity of the sine-square block. There is no assumed positivity of an unknown operator or independent convolution inequality.

Exact pinned declaration signature (source only): theorem mean_nonneg {c : ℕ} (hc : 2 ≤ c) : 0 ≤ mean c

**Theorem 1.11 (The actual von Mangoldt Dirichlet convolution).**

$$\operatorname{AtLeastTwo}(c)\Rightarrow\operatorname{R}(c)=\operatorname{div}(\operatorname{LambdaConvolution}(c), \operatorname{sqrt}(c))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.resonantMass_eq_convolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>=2, R(c)=((ArithmeticFunction.vonMangoldt*ArithmeticFunction.vonMangoldt)(c))/sqrt(c). The product here is Dirichlet convolution, equivalently the ordered divisor-antidiagonal sum of Lambda(p)*Lambda(q) with p*q=c. The endpoints with a factor 1 vanish because Lambda(1)=0. The weight identity uses sqrt(p*q)=sqrt(p)*sqrt(q), not multiplicativity of Lambda. Prime powers and ordered self-pairs are retained.

Exact pinned declaration signature (source only): theorem resonantMass_eq_convolution {c : ℕ} (hc : 2 ≤ c) :     resonantMass c =       ((ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt) c) /         Real.sqrt (c : ℝ)

**Theorem 1.12 (The exact mean in convolution form).**

$$\operatorname{AtLeastTwo}(c)\Rightarrow\operatorname{mu}(c)=\operatorname{div}(\operatorname{D}(c)-\operatorname{div}(\operatorname{LambdaConvolution}(c), \operatorname{sqrt}(c)), 2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.mean_eq_convolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>=2, mean(c)=(primeSquareMass(c)-(Lambda*Lambda)(c)/sqrt(c))/2. This consumes the actual resonantMass_eq_convolution identity. The square-root normalization and outer factor 1/2 remain unchanged.

Exact pinned declaration signature (source only): theorem mean_eq_convolution {c : ℕ} (hc : 2 ≤ c) :     mean c = (primeSquareMass c -       (ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt) c /         Real.sqrt (c : ℝ)) / 2

**Theorem 1.13 (Three distinct prime factors annihilate the convolution).**

$$\operatorname{AtLeastThreeDistinctPrimeFactors}(c)\Rightarrow\operatorname{LambdaConvolution}(c)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.convolution_zero_of_three_primeFactors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural c, assume 3<=c.primeFactors.card, where primeFactors is a finset of DISTINCT prime divisors, not prime factors counted with multiplicity. Then (Lambda*Lambda)(c)=0. A nonzero Lambda factor is supported on a prime power, hence has exactly one distinct prime divisor; two such factors can supply at most two distinct primes. The declaration has only the cardinality hypothesis. It does not discard higher powers or classify by the total number of prime factors with multiplicity.

Exact pinned declaration signature (source only): theorem convolution_zero_of_three_primeFactors {c : ℕ}     (hcard : 3 ≤ c.primeFactors.card) :     (ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt) c = 0

**Theorem 1.14 (The half-diagonal mean on the distinct-prime class).**

$$\operatorname{AtLeastTwo}(c)\land\operatorname{AtLeastThreeDistinctPrimeFactors}(c)\Rightarrow\operatorname{mu}(c)=\operatorname{div}(\operatorname{D}(c), 2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.mean_of_three_primeFactors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>=2 with 3<=c.primeFactors.card, mean(c)=primeSquareMass(c)/2. This consumes the convolution-zero theorem and the exact mean identity; it is not an assumption or a change to the general mean definition.

Exact pinned declaration signature (source only): theorem mean_of_three_primeFactors {c : ℕ} (hc : 2 ≤ c)     (hcard : 3 ≤ c.primeFactors.card) : mean c = primeSquareMass c / 2

**Theorem 1.15 (The actual convergent tail with the refined mean).**

$$\operatorname{AtLeastTwo}(c)\land\operatorname{Positive}(N)\Rightarrow\operatorname{Summable}(\operatorname{PrimeEnergySequence}(c, N))\land\operatorname{PrimeEnergyTsum}(c, N)\leq\operatorname{B3}(c, N)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.prime_symbol_square_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>=2 and N>0, the nonnegative sequence j |-> S(c,N+j+1)^2*W(N,j) is summable and its actual tsum is <=tailBudget(c,N). Here W(N,j)=((N:R)+(j:R)+1)^(-2), and j enumerates every integer m>N exactly once. The source reuses T2 finite_abel_majorant and the inverse-square partial-sum comparison. Summability follows from bounded nonnegative partial sums before using the tsum estimate. The private tail_partial proof and this public signature preserve the pinned source bytes; actual elaboration and kernel acceptance remain pending.

Exact pinned declaration signature (source only): theorem prime_symbol_square_tail {c N : ℕ} (hc : 2 ≤ c) (hN : 0 < N) :     Summable (fun j : ℕ =>       primeSymbol c ((N + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight N j) ∧     (∑' j : ℕ, primeSymbol c ((N + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight N j) ≤       tailBudget c N

**Theorem 1.16 (The refined tail retains arbitrary complex coefficients).**

$$\operatorname{AtLeastTwo}(c)\land\operatorname{Positive}(N)\Rightarrow\operatorname{Summable}(\operatorname{ComplexPrimeEnergySequence}(c, N, beta))\land\operatorname{ComplexPrimeEnergyTsum}(c, N, beta)\leq\operatorname{normSq}(beta) \operatorname{B3}(c, N)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.complex_prime_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>=2, N>0 and arbitrary beta:C, j |-> norm(beta*(S(c,N+j+1):C)/(N+j+1:C))^2 is summable. Its tsum is <=norm(beta)^2*tailBudget(c,N). No reality, vanishing, coefficient parity or spacing premise is imposed, and the exact squared complex norm is retained.

Application exposition, pending actual checking: let k,N be natural numbers with k>0 and N>0, let beta:C be arbitrary, and substitute c=5040*k. Then c>=2 and c!=0. The distinct primes 2,3,5 each divide 5040, hence each divides 5040*k. Thus {2,3,5} is a subset of c.primeFactors and 3<=c.primeFactors.card; this card counts distinct primes, not multiplicities. Applying convolution_zero_of_three_primeFactors gives (ArithmeticFunction.vonMangoldt*ArithmeticFunction.vonMangoldt)(c)=0. The generic resonantMass_eq_convolution then gives R(c)=0, and mean_of_three_primeFactors gives mean(c)=primeSquareMass(c)/2.

Apply this existing complex_prime_tail at c=5040*k with hc:2<=5040*k, hN:0<N and the same arbitrary beta, then unfold tailBudget and substitute that mean identity. The exact consequence is Summable (j |-> norm(beta*(primeSymbol(5040*k,((N+j+1:Nat):Int)):C)/((N+j+1:Nat):C))^2), together with sum_{j:Nat} norm(beta*(primeSymbol(5040*k,((N+j+1:Nat):Int)):C)/((N+j+1:Nat):C))^2 <= norm(beta)^2*(primeSquareMass(5040*k)/2/(N:R)+offset(5040*k)/((N:R)+1)^2), where the sum is the actual tsum and j enumerates every m>N once. The norm(beta)^2 factor, the half-diagonal leading constant and the full offset are retained exactly. In particular offset(c)=(primeCross(c)+sumCross(c))/2, with factor 2 per ordered pair in each channel, including nonresonant diagonal pairs in sumCross. Every higher prime power remains in I(c); beta is not assumed real or zero. This is exposition of an existing result application, not a new mathematical declaration or Describe node.

Endpoint exposition and candidates for later transient exact checks: at c=2 the interval Ico(2,2) is empty, so primeSymbol(2) is the zero function on the integers and primeSquareMass(2)=resonantMass(2)=mean(2)=offset(2)=0. For every natural c the zero lattice mode has primeSymbol(c,0)=0. These endpoint checks are not retained Lean declarations or examples, and no actual transient check has been run.

The pinned downstream source relationship is ActualFullSymbolTail -> T3.prime_symbol_square_tail. PhysicalPrimeTwoCutoff and PhysicalCompressedCosineMatrix do not consume T3 or this 5040 application. No RH, Robin inequality, signed-form positivity or physical operator identification/positivity is established. Lean/kernel/axiom checks, Scribe emission, Reg, required CI and delivery remain pending.

Exact pinned declaration signature (source only): theorem complex_prime_tail {c N : ℕ} (hc : 2 ≤ c) (hN : 0 < N) (β : ℂ) :     Summable (fun j : ℕ =>       ‖β * (primeSymbol c ((N + j + 1 : ℕ) : ℤ) : ℂ) / ((N + j + 1 : ℕ) : ℂ)‖ ^ 2) ∧     (∑' j : ℕ,       ‖β * (primeSymbol c ((N + j + 1 : ℕ) : ℤ) : ℂ) / ((N + j + 1 : ℕ) : ℂ)‖ ^ 2) ≤         ‖β‖ ^ 2 * tailBudget c N

**Theorem 1.17 (The exact universal positive mean bound).**

$$3\leq c\Rightarrow\operatorname{div}(\operatorname{square}(\operatorname{log}(2)), 4)\leq\operatorname{mean}(c)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.prime_symbol_mean_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

SOURCE_ONLY_UNCOMPILED. Exact new declaration: theorem prime_symbol_mean_lower_bound {c : ℕ} (hc : 3 ≤ c) : (Real.log (2 : ℝ)) ^ 2 / 4 ≤ mean c. The original mean is (primeSquareMass c - resonantMass c)/2, with I(c)=Ico(2,c), primeWeight(q)=vonMangoldt(q)/sqrt(q), and every ordered product p*q=c retained, including self-pairs. This is a new strict uniform lower bound; it does not follow by specializing the old mean_nonneg statement. All earlier declarations, proof bodies and Describe entries remain byte-identical.

The local consumed matching estimate applies to arbitrary real weights on any finite set of positive naturals. For the filtered ordered resonant edge set E, multiplication cancellation makes both projections injective. If q0 does not divide c, neither projection can take q0. The inequality 2*a(p)*a(q) <= a(p)^2+a(q)^2, summed over E and combined with the pinned Finset.sum_le_sum_of_injOn twice, gives R <= sum_{p in s.erase(q0)} a(p)^2. Restoring the erased term gives mean(c) >= a(q0)^2/2. Self-pairs obey exactly the same inequality; no positivity assumption on generic a, new spacing assumption, injectivity premise or change of constant is introduced.

The exhaustive symbolic split chooses q0=2 when 2 does not divide c, q0=3 when 2 divides c but 3 does not, and q0=5 when 2 and 3 divide c but 5 does not. The cutoff inequalities follow from c>=3 and these divisibilities. If all three primes divide c, their primeFactors membership gives at least three distinct prime divisors and the existing mean_of_three_primeFactors yields mean=D/2; the q=2 diagonal term suffices. This is a proof for every natural c>=3, not a finite verified cutoff table; all higher prime powers remain in both full sums.

The weight estimates use the actual vonMangoldt_apply_prime identity and Real.sq_sqrt. Exact monotonicity of log on 2^3<=3^2 gives 3*log(2)<=2*log(3); on 2^2<=5 it gives 2*log(2)<=log(5). Squaring nonnegative sides proves that each chosen weight contributes at least log(2)^2/4. At c=3, I(c) contains only 2 and has no resonant pair, so the constant is attained; this equality is narrative only, without a named fixed-cutoff corollary. At c=2 the actual mean is zero. The Reg dependence proof evaluates that degenerate fiber and uses the new theorem to obtain positive mean at 3.

The only new owner declaration is this theorem. All matching, defect and logarithm estimates are local proof steps consumed in its live derivation. The Reg candidate observes the actual mean c operand, retains the full implicit c and explicit hc telescope, keeps every natural c as state, uses enrolled DependentFamily.realize and familyRecord=none, and records continuation unknown. Actual law, whole-family rejection, sensitivity and actual dependence are supplied as uncompiled proof candidates. Source path, reconstruction, enrollment, kernel, axiom closure, Reg acceptance and Scribe discovery/emission remain pending. The eleven older public T3 targets have no supplied Reg mirror and are not claimed registered.

For c=5040*k with positive k, the same generic bound applies and the existing three-prime-factor identity additionally gives mean=D/2. This is substantive application narrative only: no named 5040, fixed-c or lower-block corollary is added. The result concerns the arithmetic prime-symbol mean. It establishes no RH/Robin result, full-Weil or signed-form positivity, accepted proof, or literature novelty. Utility:none: the new content is a universal finite-sum estimate with unbounded cutoff, not bounded enumeration, a checker, numeric reduction or certified instance.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.complex_prime_tail`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.convolution_zero_of_three_primeFactors`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.difference_resonance`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.mean`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.mean_eq_convolution`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.mean_nonneg`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.mean_of_three_primeFactors`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.offset`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.offset_nonneg`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.prime_symbol_exact_block`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.prime_symbol_mean_lower_bound`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.prime_symbol_square_tail`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.resonantMass`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.resonantMass_eq_convolution`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.sumCross`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.sum_resonance`
- Truth anchor: `D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.tailBudget`
- Dependency: [D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare](PrimeSymbolMeanSquare.md)
