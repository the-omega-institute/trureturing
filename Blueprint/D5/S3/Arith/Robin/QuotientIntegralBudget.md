# Quotient Integral Budget

## Abstract

Actual quotient residual blocks have separate head and logarithmic tail payments before infinite integral exchange.

Let K(y) be the finite prefix of k(n) over positive integers n<=floor(y), G(y)=A*y*log(y)-D*y and R=K-G. The real coefficients A,D are arbitrary. Assume independent C,mu>=0, 0<=k(n)<=C*log(n) for every n>=1, and |R(y)|<=mu*(1+log(y)) for every y>=1. The coefficient assumptions imply k(1)=0. On 0<y<1 the actual residual is D*y-A*y*log(y).

For x>1 use the existing Robin weight w(t)=(1+log(t))/(t^2*log(t)^2) and W(x)=(1+log(x))/log(x)^2. Define Q(x,m) as the integral on t>x of |R(t/m)-R(t/(m+1))|*w(t). This absolute value is taken inside the integral. Put a2=C+|A|, a1=C+2*|A|*(1+log(2))+2*|D|+2*mu and a0=4*mu.

**Theorem 1.1 (The original prefix is a fixed finite sum with a right-closed cutoff).**

Lean statement: `D5/S3/Arith/Robin/QuotientIntegralBudget.prefix_as_finite_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/QuotientIntegralBudget.prefix_as_finite_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real coefficients k, 0<=y<=N with natural N, arithmeticPrefix(k,y) equals the sum over i<N of k(i+1) when i+1<=y and zero otherwise. This original supplier is exposed for reuse by the actual von Mangoldt band composition; its statement and proof are unchanged.

**Theorem 1.2 (The original prefix difference selects exactly the directed cutoff atoms).**

Lean statement: `D5/S3/Arith/Robin/QuotientIntegralBudget.prefix_difference_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/QuotientIntegralBudget.prefix_difference_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary k and 0<=c*y<=y<=N, the prefix at y minus the prefix at c*y is the fixed finite sum with indicator c*y<i+1<=y. The lower atom is excluded and the upper atom retained. The original proof is reused without duplication.

**Theorem 1.3 (The actual residual blocks are integrable with separate first and quadratic logarithmic budgets).**

Lean statement: `D5/S3/Arith/Robin/QuotientIntegralBudget.quotientIntegralProducer`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/QuotientIntegralBudget.quotientIntegralProducer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every x>1 the actual weighted absolute block is integrable for every m>=1. The first block obeys Q(x,1)<=W(x)*(mu*(3+2*log(2))+|D|+|A|*log(2)). Every m>=2 obeys Q(x,m)<=W(x)/m^2*(a2*log(m)^2+a1*log(m)+a0).

With c=m/(m+1), each finite prefix jump has support [n,n/c). The low domain is enlarged to 1/m<=y<=m and its finite jump sum is integrated before any infinite exchange. Exact jump masses and a smooth log-product majorant pay this domain. The centered residual envelope pays y>m, retaining the actual residual instead of separately integrating unsigned K and G on the tail.

**Theorem 1.4 (Every strict tail has its explicit logarithmic payment).**

Lean statement: `D5/S3/Arith/Robin/QuotientIntegralBudget.quotient_logarithmic_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/QuotientIntegralBudget.quotient_logarithmic_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let B>=0 and assume the explicit inequality |H(m)|<=B*m/log(m)^4 for every m>=2. For every M>=2 the strict tail sum over m>M of |H(m)|*Q(x,m) is at most B*W(x)*(a2/log(M)+a1/(2*log(M)^2)+a0/(3*log(M)^3)). The strict enumeration is m=n+M+1, and reciprocal-log integral tests pay the three terms with their exact factors 1, 1/2 and 1/3.

**Theorem 1.5 (The signed series has integrable blocks and a complete norm budget).**

Lean statement: `D5/S3/Arith/Robin/QuotientIntegralBudget.quotient_signed_integral_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/QuotientIntegralBudget.quotient_signed_integral_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same hypotheses define F(m,t)=H(m)*(R(t/m)-R(t/(m+1)))*w(t). Every positive-index F(m) is integrable on t>x, and the integral of its pointwise norm equals |H(m)|*Q(x,m). The sequence of these norm integrals is summable. H(1) is unrestricted and its norm integral is at most |H(1)| times the separate first-block budget. Every strict norm tail has the preceding explicit bound.

These integrable blocks and summable integrals of their pointwise norms supply the premises of Mathlib's integral_tsum_of_summable_integral_norm. That existing Fubini result is the downstream supplier. The coefficient and residual envelopes do not prove the independent H growth hypothesis, the complete Robin inequality or the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Arith/Robin/QuotientIntegralBudget.prefix_as_finite_sum`
- Truth anchor: `D5/S3/Arith/Robin/QuotientIntegralBudget.prefix_difference_finite`
- Truth anchor: `D5/S3/Arith/Robin/QuotientIntegralBudget.quotientIntegralProducer`
- Truth anchor: `D5/S3/Arith/Robin/QuotientIntegralBudget.quotient_logarithmic_tail`
- Truth anchor: `D5/S3/Arith/Robin/QuotientIntegralBudget.quotient_signed_integral_budget`
- Dependency: [D5/S3/Arith/Robin/MellinWeightedVariation](MellinWeightedVariation.md)
