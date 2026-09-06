# Hidden Arithmetic Weight

## Abstract

Actual coprime divisor Gibbs laws identify the hidden log partition through the conditional entropy of the observer-first graph and the full-law hidden log moment.

All natural-number carriers below live in Type 0. Div(n) is the subtype of Nat.divisors n, and v(d) denotes its underlying natural value, embedded in the reals in powers and logarithms. Every logarithm is natural. The symbols w, Z and m denote weight, partition and mass. P(f,p) denotes the finite pushforward of p along f; H and C denote shannonEntropy and conditionalEntropy. In C the first coordinate is the conditioning observer. Each pair statement quantifies over positive natural J and T with gcd(J,T)=1. The symbols e, q and r denote mulEquiv, qJ and qT for exactly these hypotheses. The parameter s ranges independently over all real numbers.

**Definition 1.1 (Actual divisor carrier).**

$$\forall n \in \mathbb{N}, Div\left(n\right) = \{d \in \mathbb{N} \mid d \in divisors\left(n\right)\}$$

*Formalization.* `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.Div` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier contains precisely the natural divisors in Nat.divisors n. The zero integer has the library's empty divisor carrier.

**Definition 1.2 (Real power weight).**

$$\forall n \in \mathbb{N}, \forall s \in \mathbb{R}, \forall d \in Div\left(n\right), w\left(s, d\right) = v\left(d\right)^{-s}$$

*Formalization.* `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weight is defined directly from the actual divisor value, independently of entropy.

**Definition 1.3 (Finite partition).**

$$\forall n \in \mathbb{N}, \forall s \in \mathbb{R}, Z\left(n, s\right) = \sum_{d \in Div\left(n\right)} w\left(s, d\right)$$

*Formalization.* `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.partition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Z(n,s) is a finite sum over the actual divisor subtype.

**Definition 1.4 (Normalized weight).**

$$\forall n \in \mathbb{N}, \forall s \in \mathbb{R}, \forall d \in Div\left(n\right), m\left(n, s, d\right) = \frac{w\left(s, d\right)}{Z\left(n, s\right)}$$

*Formalization.* `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.mass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This definition uses total real division. Positivity and normalization for positive n are proved below and are not assumptions in the definition.

**Definition 1.5 (Actual multiplication equivalence).**

$$\begin{aligned}\forall J \in \mathbb{N}, \forall T \in \mathbb{N}, \\(0 < J \land 0 < T \land \gcd(J,T) = 1) \Rightarrow\\e : Equiv\left(Div\left(J\right) \times Div\left(T\right), Div\left(J \cdot T\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.mulEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward function sends (a,b) to the divisor with value v(a)v(b). Equiv.ofBijective supplies its inverse after coprime injectivity and the actual divisor-image identity prove bijectivity.

**Definition 1.6 (Observed inverse coordinate).**

$$\begin{aligned}\forall J \in \mathbb{N}, \forall T \in \mathbb{N}, \\(0 < J \land 0 < T \land \gcd(J,T) = 1) \Rightarrow\\\forall d \in Div\left(J \cdot T\right), q\left(d\right) = fst\left(\left(e^{-1}\right)\left(d\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.qJ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

q(d) is the first coordinate of e inverse applied to the full divisor d.

**Definition 1.7 (Hidden inverse coordinate).**

$$\begin{aligned}\forall J \in \mathbb{N}, \forall T \in \mathbb{N}, \\(0 < J \land 0 < T \land \gcd(J,T) = 1) \Rightarrow\\\forall d \in Div\left(J \cdot T\right), r\left(d\right) = snd\left(\left(e^{-1}\right)\left(d\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.qT` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

r(d) is the second coordinate of e inverse applied to the full divisor d.

**Theorem 1.8 (Multiplication value law).**

$$\begin{aligned}\forall J \in \mathbb{N}, \forall T \in \mathbb{N}, \\(0 < J \land 0 < T \land \gcd(J,T) = 1) \Rightarrow\\\forall a \in Div\left(J\right), \forall b \in Div\left(T\right), v\left(e\left((a, b)\right)\right) = v\left(a\right) \cdot v\left(b\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.divisor_mul_equiv_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equivalence's forward value is actual natural multiplication.

**Theorem 1.9 (Unique divisor splitting).**

$$\begin{aligned}\forall J \in \mathbb{N}, \forall T \in \mathbb{N}, \\(0 < J \land 0 < T \land \gcd(J,T) = 1) \Rightarrow\\\forall d \in Div\left(J \cdot T\right), \exists! u \in Div\left(J\right) \times Div\left(T\right), v\left(fst\left(u\right)\right) \cdot v\left(snd\left(u\right)\right) = v\left(d\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.divisor_split_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each full divisor has a unique factor pair. Coprimality supplies injectivity separately from the finset image theorem that supplies surjectivity.

**Theorem 1.10 (Positive partition at every real exponent).**

$$\forall n \in \mathbb{N}, \forall s \in \mathbb{R}, (0 < n) \Rightarrow 0 < Z\left(n, s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.partition_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every divisor weight is positive and divisor one witnesses a nonempty sum.

**Theorem 1.11 (Coprime partition product).**

$$\begin{aligned}\forall J \in \mathbb{N}, \forall T \in \mathbb{N}, \forall s \in \mathbb{R}, \\(0 < J \land 0 < T \land \gcd(J,T) = 1) \Rightarrow\\Z\left(J \cdot T, s\right) = Z\left(J, s\right) \cdot Z\left(T, s\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.partition_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Real power multiplicativity and reindexing through the actual multiplication equivalence factor the finite sum.

**Theorem 1.12 (Strictly positive divisor mass).**

$$\forall n \in \mathbb{N}, \forall s \in \mathbb{R}, (0 < n) \Rightarrow \forall d \in Div\left(n\right), 0 < m\left(n, s, d\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.mass_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive weight divided by the positive finite partition is positive.

**Theorem 1.13 (Actual normalization).**

$$\forall n \in \mathbb{N}, \forall s \in \mathbb{R}, (0 < n) \Rightarrow \sum_{d \in Div\left(n\right)} m\left(n, s, d\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.mass_total` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing the independently defined quotient gives one.

**Theorem 1.14 (Actual mass product).**

$$\begin{aligned}\forall J \in \mathbb{N}, \forall T \in \mathbb{N}, \forall s \in \mathbb{R}, \\(0 < J \land 0 < T \land \gcd(J,T) = 1) \Rightarrow\\\forall a \in Div\left(J\right), \forall b \in Div\left(T\right), m\left(J \cdot T, s, e\left((a, b)\right)\right) = m\left(J, s, a\right) \cdot m\left(T, s, b\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.mass_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The weight and partition product laws give the product of the two actual masses.

**Theorem 1.15 (Full splitting law).**

$$\begin{aligned}\forall J \in \mathbb{N}, \forall T \in \mathbb{N}, \forall s \in \mathbb{R}, \\(0 < J \land 0 < T \land \gcd(J,T) = 1) \Rightarrow\\P\left((d \mapsto (q\left(d\right), r\left(d\right))), m\left(J \cdot T, s\right)\right) = (u \mapsto m\left(J, s, fst\left(u\right)\right) \cdot m\left(T, s, snd\left(u\right)\right))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.split_pushforward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the right u ranges over Div(J) times Div(T). The identity transports the original full-divisor law to the independently defined product mass.

**Theorem 1.16 (Actual observed marginal).**

$$\begin{aligned}\forall J \in \mathbb{N}, \forall T \in \mathbb{N}, \forall s \in \mathbb{R}, \\(0 < J \land 0 < T \land \gcd(J,T) = 1) \Rightarrow\\P\left(q, m\left(J \cdot T, s\right)\right) = m\left(J, s\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.observer_pushforward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pushforward composition with the first projection and hidden normalization identify the observed law.

**Theorem 1.17 (Actual hidden marginal).**

$$\begin{aligned}\forall J \in \mathbb{N}, \forall T \in \mathbb{N}, \forall s \in \mathbb{R}, \\(0 < J \land 0 < T \land \gcd(J,T) = 1) \Rightarrow\\P\left(r, m\left(J \cdot T, s\right)\right) = m\left(T, s\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.hidden_pushforward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pushforward composition with the second projection and observed normalization identify the hidden law.

**Theorem 1.18 (Full-law hidden log expectation).**

$$\begin{aligned}\forall J \in \mathbb{N}, \forall T \in \mathbb{N}, \forall s \in \mathbb{R}, \\(0 < J \land 0 < T \land \gcd(J,T) = 1) \Rightarrow\\(\sum_{d \in Div\left(J \cdot T\right)} m\left(J \cdot T, s, d\right) \cdot \log (v\left(r\left(d\right)\right))) = (\sum_{d \in Div\left(T\right)} m\left(T, s, d\right) \cdot \log (v\left(d\right)))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.hidden_log_expectation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual hidden marginal transports the full-law logarithmic expectation.

**Theorem 1.19 (Observer-first graph entropy).**

$$\begin{aligned}\forall J \in \mathbb{N}, \forall T \in \mathbb{N}, \forall s \in \mathbb{R}, \\(0 < J \land 0 < T \land \gcd(J,T) = 1) \Rightarrow\\C\left(P\left((d \mapsto (q\left(d\right), d)), m\left(J \cdot T, s\right)\right)\right) = H\left(m\left(T, s\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.observer_conditional_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The injective splitting transports full entropy to product entropy. Public product mutual-information identities give entropy additivity, and the public quotient fiber decomposition identifies the graph conditional entropy. The graph is d mapped to (q(d),d), so the quantity is H(D given D_J).

**Theorem 1.20 (Pointwise divisor surprisal).**

$$\forall n \in \mathbb{N}, \forall s \in \mathbb{R}, (0 < n) \Rightarrow \forall d \in Div\left(n\right), -\log (m\left(n, s, d\right)) = s \cdot \log (v\left(d\right)) + \log (Z\left(n, s\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.neg_log_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive divisor values and a positive partition justify the logarithm of the quotient and the real power. There is no sign restriction on s.

**Theorem 1.21 (Finite divisor Gibbs entropy).**

$$\forall n \in \mathbb{N}, \forall s \in \mathbb{R}, (0 < n) \Rightarrow H\left(m\left(n, s\right)\right) = s \cdot (\sum_{d \in Div\left(n\right)} m\left(n, s, d\right) \cdot \log (v\left(d\right))) + \log (Z\left(n, s\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.gibbs_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiply the pointwise surprisal by mass, sum over actual divisors, and use normalization. No infinite series or division by s is used.

**Theorem 1.22 (Hidden arithmetic weight formula).**

$$\begin{aligned}\forall J \in \mathbb{N}, \forall T \in \mathbb{N}, \forall s \in \mathbb{R}, \\(0 < J \land 0 < T \land \gcd(J,T) = 1) \Rightarrow\\\log (Z\left(T, s\right)) = C\left(P\left((d \mapsto (q\left(d\right), d)), m\left(J \cdot T, s\right)\right)\right) - s \cdot (\sum_{d \in Div\left(J \cdot T\right)} m\left(J \cdot T, s, d\right) \cdot \log (v\left(r\left(d\right)\right)))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.hidden_arithmetic_weight_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the real-parameter actual-divisor consumer of the first chapter's Theorem 5.5 in ZECKENDORF_EULER_5040. It combines the graph entropy, hidden expectation transport, and finite Gibbs identity. The alternate observer recording all observed prime exponents would require its own value-preserving equivalence and is not established here. Neighboring coarse-graining and collision-escape clauses are separate.

## References

- Truth anchor: `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.Div`
- Truth anchor: `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.divisor_mul_equiv_val`
- Truth anchor: `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.divisor_split_unique`
- Truth anchor: `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.gibbs_entropy`
- Truth anchor: `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.hidden_arithmetic_weight_formula`
- Truth anchor: `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.hidden_log_expectation`
- Truth anchor: `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.hidden_pushforward`
- Truth anchor: `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.mass`
- Truth anchor: `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.mass_mul`
- Truth anchor: `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.mass_pos`
- Truth anchor: `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.mass_total`
- Truth anchor: `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.mulEquiv`
- Truth anchor: `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.neg_log_mass`
- Truth anchor: `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.observer_conditional_entropy`
- Truth anchor: `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.observer_pushforward`
- Truth anchor: `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.partition`
- Truth anchor: `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.partition_mul`
- Truth anchor: `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.partition_pos`
- Truth anchor: `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.qJ`
- Truth anchor: `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.qT`
- Truth anchor: `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.split_pushforward`
- Truth anchor: `D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.weight`
- Dependency: [D5/S3/Entropy/Forgetting/PushforwardComposition](../../Entropy/Forgetting/PushforwardComposition.md)
- Dependency: [D5/S3/Entropy/Fusion/QuotientFiberDecomposition](../../Entropy/Fusion/QuotientFiberDecomposition.md)
- Dependency: [D5/S3/Entropy/MutualInformationEntropy](../../Entropy/MutualInformationEntropy.md)
- Dependency: [D5/S3/Entropy/MutualInformationProduct](../../Entropy/MutualInformationProduct.md)
