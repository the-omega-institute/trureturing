# Actual Two-Price Defect and the Full Layer Maximum

## Abstract

Exact pressure defects for the strict all-layer integer and the constructed weak-layer maximum.

All variables in the displays have their indicated real or natural types. valuation(n,p) means n.factorization(p), Prime means Nat.Prime, Icc and uIcc are closed and unordered closed intervals, and Finite means set finiteness. All integrals use the real variable shown by the differential and Lebesgue measure. Proof arguments are suppressed only when proof-irrelevant; the positive-price argument of weakLayerExponents is displayed. IsGoldenResourceOptimal(q,n) compares goldenResourceObjective(q,m) with goldenResourceObjective(q,n) for every natural m at least 1. The objective is log of the reciprocal-divisor sum minus q times log(n). goldenLayerMarginal(p,k) is log((1-(1/p)^(k+1))/(1-(1/p)^k))/log(p). These are the actual imported functions.

**Definition 1.1 (strictInteger).**

$$\forall q \in \mathbb{R},\; \operatorname{strictInteger}\left(q\right) = \left(\operatorname{if} hq:\left(0 < q\right) \operatorname{then} \operatorname{choose}\left(\operatorname{optimalLayerCountSpec}\left(q, hq\right)\right) \operatorname{else} 1\right)$$

*Formalization.* `D5/S3/Arith/Robin/ActualTwoPriceDefect.strictInteger` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For positive q, choose exactly the integer supplied by optimal_layer_count_spec. It has every strict positive layer and divides every positive optimizer. The value at nonpositive q is the total-definition convention 1. optimalLayerCountSpec denotes that existing existence proof with its positive-price argument.

**Theorem 1.2 (strictInteger pos).**

$$\forall q \in \mathbb{R},\; 0 < q \Rightarrow 1 \le \operatorname{strictInteger}\left(q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualTwoPriceDefect.strictInteger_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The chosen strict inventory is a positive natural integer at every positive price.

**Theorem 1.3 (strictInteger counts).**

$$\forall q \in \mathbb{R},\; 0 < q \Rightarrow \left(\forall p \in \mathbb{N},\; \operatorname{valuation}\left(\operatorname{strictInteger}\left(q\right), p\right) = \operatorname{optimalLayerCount}\left(q, p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualTwoPriceDefect.strictInteger_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every natural prime direction has the original strict count; nonprime directions are included as zero directions.

**Theorem 1.4 (strict layer iff).**

$$\forall q \in \mathbb{R},\; 0 < q \Rightarrow \left(\forall p \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{Prime}\left(p\right) \Rightarrow \left(1 \le k \Rightarrow \left(k \le \operatorname{valuation}\left(\operatorname{strictInteger}\left(q\right), p\right) \Leftrightarrow q < \operatorname{goldenLayerMarginal}\left(p, k\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualTwoPriceDefect.strict_layer_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prime and every positive layer index, occupation is equivalent to a strict price inequality. Equality layers are excluded.

**Theorem 1.5 (strictInteger eq product).**

$$\forall q \in \mathbb{R},\; 0 < q \Rightarrow \operatorname{strictInteger}\left(q\right) = \prod_{\left(p:\mathbb{N}\right) \in \operatorname{primeFactors}\left(\operatorname{strictInteger}\left(q\right)\right)} \left(p^{\operatorname{optimalLayerCount}\left(q, p\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualTwoPriceDefect.strictInteger_eq_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product reconstructs the same chosen strict integer from all of its prime directions, using the original strict layer counts.

**Theorem 1.6 (weak layers finite).**

$$\forall q \in \mathbb{R},\; 0 < q \Rightarrow \operatorname{Finite}\left(\left\{pk:\mathbb{N} \times \mathbb{N} \mid 1 \le \operatorname{snd}\left(pk\right) \land \left(\operatorname{Prime}\left(\operatorname{fst}\left(pk\right)\right) \land q \le \operatorname{goldenLayerMarginal}\left(\operatorname{fst}\left(pk\right), \operatorname{snd}\left(pk\right)\right)\right)\right\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualTwoPriceDefect.weak_layers_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a positive price the entire set of weak layers is finite. Both prime and positive exponent indices range over all naturals, and every equality layer is included.

**Definition 1.7 (weakLayerCount).**

$$\forall q \in \mathbb{R},\; \forall p \in \mathbb{N},\; \operatorname{weakLayerCount}\left(q, p\right) = \operatorname{ncard}\left(\left\{k:\mathbb{N} \mid 1 \le k \land \left(\operatorname{Prime}\left(p\right) \land q \le \operatorname{goldenLayerMarginal}\left(p, k\right)\right)\right\}\right)$$

*Formalization.* `D5/S3/Arith/Robin/ActualTwoPriceDefect.weakLayerCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural set cardinality counts all weak layers in a direction. This is a total definition; finiteness is asserted separately at positive prices.

**Theorem 1.8 (weak layers eq count interval).**

$$\forall q \in \mathbb{R},\; 0 < q \Rightarrow \left(\forall p \in \mathbb{N},\; \operatorname{Prime}\left(p\right) \Rightarrow \left\{k:\mathbb{N} \mid 1 \le k \land \left(\operatorname{Prime}\left(p\right) \land q \le \operatorname{goldenLayerMarginal}\left(p, k\right)\right)\right\} = \operatorname{Icc}\left(1, \operatorname{weakLayerCount}\left(q, p\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualTwoPriceDefect.weak_layers_eq_count_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strict decrease of the actual marginal makes each finite weak layer set a complete positive prefix, including its last equality layer.

**Definition 1.9 (weakLayerExponents).**

$$\forall q \in \mathbb{R},\; \forall hq \in 0 < q,\; \operatorname{weakLayerExponents}\left(q, hq\right) = \operatorname{onFinset}\left(\operatorname{image}\left(\operatorname{fst}\left(\right), \operatorname{toFinset}\left(\left\{pk:\mathbb{N} \times \mathbb{N} \mid 1 \le \operatorname{snd}\left(pk\right) \land \left(\operatorname{Prime}\left(\operatorname{fst}\left(pk\right)\right) \land q \le \operatorname{goldenLayerMarginal}\left(\operatorname{fst}\left(pk\right), \operatorname{snd}\left(pk\right)\right)\right)\right\}, \operatorname{weakLayersFinite}\left(q, hq\right)\right)\right), \left(\lambda \left(p:\mathbb{N}\right) \mapsto \left(\operatorname{weakLayerCount}\left(q, p\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/Robin/ActualTwoPriceDefect.weakLayerExponents` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite support is the image of the first projection of the entire weak-layer set. onFinset has exactly the displayed values; its proof-irrelevant support certificate is the one in weakLayerExponents. weakLayersFinite denotes weak_layers_finite, and toFinset uses that finite-set proof.

**Definition 1.10 (maximalInteger).**

$$\forall q \in \mathbb{R},\; \operatorname{maximalInteger}\left(q\right) = \left(\operatorname{if} hq:\left(0 < q\right) \operatorname{then} \operatorname{finsuppProd}\left(\operatorname{weakLayerExponents}\left(q, hq\right), \left(\lambda \left(p:\mathbb{N}\right) \mapsto \left(\left(\lambda \left(k:\mathbb{N}\right) \mapsto \left(p^{k}\right)\right)\right)\right)\right) \operatorname{else} 1\right)$$

*Formalization.* `D5/S3/Arith/Robin/ActualTwoPriceDefect.maximalInteger` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At positive q this is the finite prime-power product of weakLayerExponents. finsuppProd sums no exponents: it multiplies p raised to k over the support. At other prices its value is 1.

**Theorem 1.11 (optimizer exponent bounds).**

$$\forall q \in \mathbb{R},\; 0 < q \Rightarrow \left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\operatorname{IsGoldenResourceOptimal}\left(q, n\right) \Rightarrow \left(\forall p \in \mathbb{N},\; \operatorname{optimalLayerCount}\left(q, p\right) \le \operatorname{valuation}\left(n, p\right) \land \operatorname{valuation}\left(n, p\right) \le \operatorname{weakLayerCount}\left(q, p\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualTwoPriceDefect.optimizer_exponent_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive global optimizer has each exponent between the original strict count and the full weak count.

**Theorem 1.12 (maximalInteger spec).**

$$\forall q \in \mathbb{R},\; 0 < q \Rightarrow \left(1 \le \operatorname{maximalInteger}\left(q\right) \land \left(\left(\forall p \in \mathbb{N},\; \operatorname{valuation}\left(\operatorname{maximalInteger}\left(q\right), p\right) = \operatorname{weakLayerCount}\left(q, p\right)\right) \land \left(\operatorname{IsGoldenResourceOptimal}\left(q, \operatorname{maximalInteger}\left(q\right)\right) \land \left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\operatorname{IsGoldenResourceOptimal}\left(q, n\right) \Rightarrow \left(n \mid \operatorname{maximalInteger}\left(q\right) \land n \le \operatorname{maximalInteger}\left(q\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualTwoPriceDefect.maximalInteger_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constructed product is positive, has exactly the weak counts and is globally optimal. Every positive optimizer divides it and is at most it. No optimizer or finite-closure premise is assumed.

**Theorem 1.13 (maximalInteger all ties).**

$$\forall q \in \mathbb{R},\; 0 < q \Rightarrow \left(\operatorname{Finite}\left(\left\{pk:\mathbb{N} \times \mathbb{N} \mid 1 \le \operatorname{snd}\left(pk\right) \land \left(\operatorname{Prime}\left(\operatorname{fst}\left(pk\right)\right) \land \operatorname{goldenLayerMarginal}\left(\operatorname{fst}\left(pk\right), \operatorname{snd}\left(pk\right)\right) = q\right)\right\}\right) \land \left(\forall p \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{Prime}\left(p\right) \Rightarrow \left(1 \le k \Rightarrow \left(\left(\operatorname{valuation}\left(\operatorname{strictInteger}\left(q\right), p\right) < k \land k \le \operatorname{valuation}\left(\operatorname{maximalInteger}\left(q\right), p\right)\right) \Leftrightarrow \operatorname{goldenLayerMarginal}\left(p, k\right) = q\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualTwoPriceDefect.maximalInteger_all_ties` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All simultaneous equality layers form a finite set and are exactly the layers added between the strict and maximal integers, for every prime and every positive index.

**Definition 1.14 (price).**

$$\forall x \in \mathbb{R},\; \operatorname{price}\left(x\right) = \frac{1}{x \cdot \operatorname{log}\left(x\right)}$$

*Formalization.* `D5/S3/Arith/Robin/ActualTwoPriceDefect.price` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real price is total; its positivity and analytic use below are on x greater than 1.

**Definition 1.15 (weight).**

$$\forall x \in \mathbb{R},\; \operatorname{weight}\left(x\right) = \frac{1 + \operatorname{log}\left(x\right)}{x^{2} \cdot \operatorname{log}\left(x\right)^{2}}$$

*Formalization.* `D5/S3/Arith/Robin/ActualTwoPriceDefect.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The square applies separately to x and to log(x). The denominator is x squared times the square of log(x).

**Definition 1.16 (integerAt).**

$$\forall x \in \mathbb{R},\; \operatorname{integerAt}\left(x\right) = \operatorname{strictInteger}\left(\operatorname{price}\left(x\right)\right)$$

*Formalization.* `D5/S3/Arith/Robin/ActualTwoPriceDefect.integerAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer at x is the original strict inventory evaluated at price(x).

**Definition 1.17 (clock).**

$$\forall x \in \mathbb{R},\; \operatorname{clock}\left(x\right) = \operatorname{log}\left(\operatorname{integerAt}\left(x\right)\right)$$

*Formalization.* `D5/S3/Arith/Robin/ActualTwoPriceDefect.clock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The clock is the logarithm of that integer. It is not the price parameter x.

**Definition 1.18 (W).**

$$\forall n \in \mathbb{N},\; \operatorname{W}\left(n\right) = \operatorname{log}\left(\frac{\operatorname{real}\left(\operatorname{sigma}\left(1, n\right)\right)}{\operatorname{real}\left(n\right)}\right)$$

*Formalization.* `D5/S3/Arith/Robin/ActualTwoPriceDefect.W` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sigma(1,n) is the natural divisor sum and real denotes the natural-to-real cast. The definition uses real division and the total real logarithm.

**Definition 1.19 (pressure).**

$$\forall q \in \mathbb{R},\; \operatorname{pressure}\left(q\right) = \operatorname{sSup}\left(\left\{v:\mathbb{R} \mid \exists n \in \mathbb{N},\; 1 \le n \land v = \operatorname{goldenResourceObjective}\left(q, n\right)\right\}\right)$$

*Formalization.* `D5/S3/Arith/Robin/ActualTwoPriceDefect.pressure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This total sSup ranges over objectives of all positive natural integers. Boundedness and unconditional attainment below are proved only at positive prices.

**Definition 1.20 (defect).**

$$\forall a \in \mathbb{R},\; \forall n \in \mathbb{N},\; \operatorname{defect}\left(a, n\right) = \operatorname{pressure}\left(\operatorname{price}\left(a\right)\right) - \operatorname{W}\left(n\right) + \operatorname{price}\left(a\right) \cdot \operatorname{log}\left(n\right)$$

*Formalization.* `D5/S3/Arith/Robin/ActualTwoPriceDefect.defect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same specified integer n is evaluated at price(a). Its own logarithm is retained in the linear resource term.

**Theorem 1.21 (compact layer support).**

$$\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; 1 < a \Rightarrow \left(a \le b \Rightarrow \left(\exists S \in \operatorname{Finset}\left(\mathbb{N} \times \mathbb{N}\right),\; \left(\forall pk \in \mathbb{N} \times \mathbb{N},\; pk \in S \Rightarrow \left(1 \le \operatorname{snd}\left(pk\right) \land \operatorname{Prime}\left(\operatorname{fst}\left(pk\right)\right)\right)\right) \land \left(\forall u \in \mathbb{R},\; u \in \operatorname{Icc}\left(a, b\right) \Rightarrow \left(\forall p \in \mathbb{N},\; \forall k \in \mathbb{N},\; 1 \le k \Rightarrow \left(\operatorname{Prime}\left(p\right) \Rightarrow \left(\operatorname{price}\left(u\right) \le \operatorname{goldenLayerMarginal}\left(p, k\right) \Rightarrow \left(p, k\right) \in S\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualTwoPriceDefect.compact_layer_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One finite set contains every weakly active prime layer throughout the whole closed interval, with no exponent cutoff. The finite set also contains only prime positive layers.

**Theorem 1.22 (clock monotone).**

$$\forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; 1 < x \Rightarrow \left(1 < y \Rightarrow \left(x \le y \Rightarrow \operatorname{clock}\left(x\right) \le \operatorname{clock}\left(y\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualTwoPriceDefect.clock_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

MonotoneOn is written out with both real arguments in the open interval above 1. It follows from divisibility growth as price decreases.

**Theorem 1.23 (pressure eq of optimal).**

$$\forall q \in \mathbb{R},\; \forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\operatorname{IsGoldenResourceOptimal}\left(q, n\right) \Rightarrow \operatorname{pressure}\left(q\right) = \operatorname{goldenResourceObjective}\left(q, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualTwoPriceDefect.pressure_eq_of_optimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This conditional equality has no positive-price hypothesis. It takes a positive optimizer as input and asserts no optimizer exists at a nonpositive price.

**Theorem 1.24 (pressure maximal spec).**

$$\forall q \in \mathbb{R},\; 0 < q \Rightarrow \left(\operatorname{BddAbove}\left(\left\{v:\mathbb{R} \mid \exists n \in \mathbb{N},\; 1 \le n \land v = \operatorname{goldenResourceObjective}\left(q, n\right)\right\}\right) \land \operatorname{pressure}\left(q\right) = \operatorname{goldenResourceObjective}\left(q, \operatorname{maximalInteger}\left(q\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualTwoPriceDefect.pressure_maximal_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every positive price the proved constructed optimizer supplies an upper bound for the entire objective set and attains its real supremum.

**Theorem 1.25 (pressure integral).**

$$\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; 1 < a \Rightarrow \left(1 < b \Rightarrow \int_{a}^{b} \left(\operatorname{clock}\left(u\right) \cdot \operatorname{weight}\left(u\right)\right)\,\mathrm{d}u = \operatorname{pressure}\left(\operatorname{price}\left(b\right)\right) - \operatorname{pressure}\left(\operatorname{price}\left(a\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualTwoPriceDefect.pressure_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integral is oriented and allows a less than b, b less than a and equal endpoints. Strict left stability at every activation event supplies the one-sided derivative; reflection gives the right-sided fundamental theorem of calculus.

**Theorem 1.26 (two price oriented).**

$$\forall x \in \mathbb{R},\; \forall a \in \mathbb{R},\; 1 < x \Rightarrow \left(1 < a \Rightarrow \operatorname{defect}\left(a, \operatorname{integerAt}\left(x\right)\right) = \int_{x}^{a} \left(\left(\operatorname{clock}\left(u\right) - \operatorname{clock}\left(x\right)\right) \cdot \operatorname{weight}\left(u\right)\right)\,\mathrm{d}u\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualTwoPriceDefect.two_price_oriented` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both real centers are arbitrary above 1. The same original source integer is retained. Pressure at the comparison price is attained by the constructed full weak product; integration gives its exact comparison cost.

**Theorem 1.27 (npc5 oriented).**

$$\forall x \in \mathbb{R},\; 1 < x \Rightarrow \left(1 < \operatorname{clock}\left(x\right) \Rightarrow \operatorname{defect}\left(\operatorname{clock}\left(x\right), \operatorname{integerAt}\left(x\right)\right) = \int_{x}^{\operatorname{clock}\left(x\right)} \left(\left(\operatorname{clock}\left(u\right) - \operatorname{clock}\left(x\right)\right) \cdot \operatorname{weight}\left(u\right)\right)\,\mathrm{d}u\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualTwoPriceDefect.npc5_oriented` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set a equal to the source integer logarithm A=clock(x). Both x>1 and A>1 remain hypotheses, and the original source is integerAt(x).

**Theorem 1.28 (npc5).**

$$\forall x \in \mathbb{R},\; 1 < x \Rightarrow \left(1 < \operatorname{clock}\left(x\right) \Rightarrow \operatorname{defect}\left(\operatorname{clock}\left(x\right), \operatorname{integerAt}\left(x\right)\right) = \int_{\operatorname{min}\left(x, \operatorname{clock}\left(x\right)\right)}^{\operatorname{max}\left(x, \operatorname{clock}\left(x\right)\right)} \left(\left|\operatorname{clock}\left(u\right) - \operatorname{clock}\left(x\right)\right| \cdot \operatorname{weight}\left(u\right)\right)\,\mathrm{d}u\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualTwoPriceDefect.npc5` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both price orders and all activation ties are included. Monotonicity of the strict clock converts orientation into the absolute integrand over the sorted endpoints. The case A=clock(x)=x>1 is included in the same formulas: both integration endpoints coincide, so the oriented and absolute integrals and defect are zero. This conditional case does not assert the existence of a fixed point.

**Theorem 1.29 (npc5 any comparison optimizer).**

$$\forall x \in \mathbb{R},\; 1 < x \Rightarrow \left(1 < \operatorname{clock}\left(x\right) \Rightarrow \left(\forall C \in \mathbb{N},\; 1 \le C \Rightarrow \left(\operatorname{IsGoldenResourceOptimal}\left(\operatorname{price}\left(\operatorname{clock}\left(x\right)\right), C\right) \Rightarrow \operatorname{goldenResourceObjective}\left(\operatorname{price}\left(\operatorname{clock}\left(x\right)\right), C\right) - \operatorname{goldenResourceObjective}\left(\operatorname{price}\left(\operatorname{clock}\left(x\right)\right), \operatorname{integerAt}\left(x\right)\right) = \int_{\operatorname{min}\left(x, \operatorname{clock}\left(x\right)\right)}^{\operatorname{max}\left(x, \operatorname{clock}\left(x\right)\right)} \left(\left|\operatorname{clock}\left(u\right) - \operatorname{clock}\left(x\right)\right| \cdot \operatorname{weight}\left(u\right)\right)\,\mathrm{d}u\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualTwoPriceDefect.npc5_any_comparison_optimizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive optimizer at the source own price gives the same cost. C is an arbitrary optimizer in this conditional statement. For any x>1 with A=clock(x)>1, take q=price(A)>0 and M=maximalInteger(q). maximalInteger_spec constructs M without an optimizer certificate and proves every positive global optimizer divides M and is at most M. maximalInteger_all_ties gives the finite set of all simultaneous equality layers and, for every prime p and every k>=1, valuation(strictInteger(q),p)<k<=valuation(M,p) if and only if goldenLayerMarginal(p,k)=q. pressure_maximal_spec and the sigma identity identify defect(A,integerAt(x)) with objective(q,M)-objective(q,integerAt(x)); two_price_oriented, npc5_oriented and npc5 supply both the oriented and absolute integrals for this same source. Thus all constructed-maximal comparison clauses remain consequences of the complete general statements, including A=x and all ties, without a separate tracked conjunction.

These identities and optimizer constructions do not establish the original signed-floor estimate, NPC7, the full Robin inequality on the 5040 family, or the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.W`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.clock`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.clock_monotone`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.compact_layer_support`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.defect`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.integerAt`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.maximalInteger`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.maximalInteger_all_ties`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.maximalInteger_spec`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.npc5`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.npc5_any_comparison_optimizer`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.npc5_oriented`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.optimizer_exponent_bounds`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.pressure`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.pressure_eq_of_optimal`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.pressure_integral`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.pressure_maximal_spec`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.price`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.strictInteger`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.strictInteger_counts`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.strictInteger_eq_product`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.strictInteger_pos`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.strict_layer_iff`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.two_price_oriented`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.weakLayerCount`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.weakLayerExponents`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.weak_layers_eq_count_interval`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.weak_layers_finite`
- Truth anchor: `D5/S3/Arith/Robin/ActualTwoPriceDefect.weight`
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResource5040EndpointComparison](../GoldenResource/GoldenResource5040EndpointComparison.md)
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResourceOptimalLayerCount](../GoldenResource/GoldenResourceOptimalLayerCount.md)
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResourceThresholdCriterion](../GoldenResource/GoldenResourceThresholdCriterion.md)
- Dependency: [D5/S3/Arith/Robin/EulerLayerPhaseSeparation](EulerLayerPhaseSeparation.md)
