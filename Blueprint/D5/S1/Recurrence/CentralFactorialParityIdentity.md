# Central-Factorial Parity Identities

## Abstract

A universal half-shift factorization proves two central-factorial coefficient identities.

The two final statements match the conjectured formulas (4.27) and (4.41) in S. Yakubovich, On the generalized Dirichlet beta and Riemann zeta functions and Ramanujan-type formulae for beta and zeta values, arXiv:2405.03294, section 4. The proofs below are derived here from polynomial products and coefficient extraction. This citation identifies the questions being answered, not an external proof.

All polynomial equalities are in Q[X]. C denotes Polynomial.C, comp is polynomial composition, and coeff(P,K) is the coefficient of X^K. The notation t(N,K) denotes centralFactorial N K; A_n, C_n and F_n denote A n, Cpoly n and F n. The map rat is the natural-number cast into Q. The operator div is natural-number division, and mod is its remainder. Subtraction between natural-number indices is truncated at zero; subtraction involving rat is rational subtraction. Icc(a,b) is the inclusive natural interval, empty when b<a; range(a) is 0 through a-1. The operator choose is Nat.choose, with value zero when its lower index exceeds its upper index.

**Definition 1.1 (Signed Rational Central-Factorial Coefficients).**

$$\begin{aligned}\forall N , K \in \mathbb{N},\\\operatorname{t}(N , K): \mathbb{Q},\\(N \bmod 2 = 0) \Rightarrow \operatorname{t}(N , K) = \operatorname{coeff}(\prod_{j \in \operatorname{range}(\operatorname{div}(N , 2))} (X^{2} - \operatorname{C}(\operatorname{rat}(j)^{2})) , K),\\(N \bmod 2 \ne 0) \Rightarrow \operatorname{t}(N , K) = \operatorname{coeff}(X \cdot \prod_{j \in \operatorname{range}(\operatorname{div}(N , 2))} (X^{2} - \operatorname{C}((\operatorname{rat}(j) + \frac{1}{2})^{2})) , K).\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/CentralFactorialParityIdentity.centralFactorial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These are the defining even and odd products, including all zero coefficients. The private squareProduct abbreviation has been expanded in this display. No absolute values or odd-row rescaling enter the definition. The paper's first-kind even and odd product conventions are (1.22) and (1.24).

**Definition 1.2 (Integer-Root Odd Polynomial).**

$$\begin{aligned}\forall n \in \mathbb{N},\\A_{n} = X \cdot \prod_{j \in \operatorname{Icc}(1 , n - 1)} (X^{2} - \operatorname{C}(\operatorname{rat}(j)^{2}))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/CentralFactorialParityIdentity.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The leading X is outside the product, exactly as in the definition.

**Definition 1.3 (Half-Integer-Root Even Polynomial).**

$$\begin{aligned}\forall n \in \mathbb{N},\\C_{n} = \prod_{j \in \operatorname{Icc}(1 , n - 1)} (X^{2} - \operatorname{C}((\operatorname{rat}(j) - \frac{1}{2})^{2}))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/CentralFactorialParityIdentity.Cpoly` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The factors use j minus one half, with j starting at one.

**Theorem 1.4 (Evenness of the Half-Integer-Root Product).**

$$\begin{aligned}\forall n \in \mathbb{N},\\\operatorname{comp}(C_{n} , 0 - X) = C_{n}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/CentralFactorialParityIdentity.Cpoly_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each quadratic factor is unchanged by substituting zero minus X.

**Definition 1.5 (Scaled Shift Polynomial).**

$$\begin{aligned}\forall n \in \mathbb{N},\\F_{n} = \operatorname{C}(\frac{1}{2}) \cdot \operatorname{comp}(A_{n} , \operatorname{C}(\frac{1}{2}) \cdot (1 + X))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/CentralFactorialParityIdentity.F` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiplication by C(1/2) scales the polynomial after composition.

**Theorem 1.6 (Universal Half-Shift Factorization).**

$$\begin{aligned}\forall n \in \mathbb{N},\\(1 \le n) \Rightarrow\\\operatorname{comp}(A_{n} , X + \operatorname{C}(\frac{1}{2})) = (X + \operatorname{C}(\operatorname{rat}(n) - \frac{1}{2})) \cdot C_{n}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/CentralFactorialParityIdentity.half_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction pairs each new integer-root quadratic with the preceding linear factor. This produces the half-integer-root product uniformly in n.

**Theorem 1.7 (Scaled Linear Times Even Factorization).**

$$\begin{aligned}\forall n \in \mathbb{N},\\(1 \le n) \Rightarrow\\F_{n} = \operatorname{C}(\frac{1}{4}) \cdot (X + \operatorname{C}(2 \cdot \operatorname{rat}(n) - 1)) \cdot \operatorname{comp}(C_{n} , \operatorname{C}(\frac{1}{2}) \cdot X)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/CentralFactorialParityIdentity.F_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compose the half-shift identity with X/2 and multiply by one half. The resulting constant polynomial factor is C(1/4).

**Theorem 1.8 (Adjacent Coefficient Relation).**

$$\begin{aligned}\forall n , r \in \mathbb{N},\\(1 \le n) \Rightarrow\\\operatorname{coeff}(F_{n} , 2 \cdot r) = (2 \cdot \operatorname{rat}(n) - 1) \cdot \operatorname{coeff}(F_{n} , 2 \cdot r + 1)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/CentralFactorialParityIdentity.adjacent_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second factor is even, so each adjacent even and odd coefficient pair has the displayed ratio, including coefficients beyond the degree.

**Theorem 1.9 (Parity Identity).**

$$\begin{aligned}\forall n , k \in \mathbb{N},\\(1 \le n) \Rightarrow\\(1 \le k) \Rightarrow\\(\frac{1}{4})^{k} \cdot \operatorname{t}(2 \cdot n - 1 , 2 \cdot k - 1) = \sum_{q \in \operatorname{Icc}(k , n)} ((\frac{1}{4})^{q} \cdot \operatorname{rat}(\operatorname{choose}(2 \cdot q - 1 , 2 \cdot k - 1)) \cdot \operatorname{t}(2 \cdot n , 2 \cdot q))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/CentralFactorialParityIdentity.identity_427` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compare the odd coefficients of F in its defining expansion and its factorization. The statement covers all positive n and k, without a k<=n hypothesis. The notation (1/4)^k equals 4 raised to the integer exponent -k.

**Theorem 1.10 (Adjacent Binomial Relation).**

$$\begin{aligned}\forall p , d \in \mathbb{N},\\\operatorname{rat}(p + 1) \cdot \operatorname{rat}(\operatorname{choose}(p , d)) = (\operatorname{rat}(\operatorname{choose}(p , d)) + \operatorname{rat}(\operatorname{choose}(p , d + 1))) \cdot \operatorname{rat}(d + 1)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/CentralFactorialParityIdentity.choose_adjacent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive j and l, specialize p=2j-1 and d=l-1 to obtain the named 2j and l relation. The proof applies Mathlib's Nat.add_one_mul_choose_eq, rewrites with Nat.choose_succ_succ', and casts the equality into Q.

**Theorem 1.11 (Weighted Sum Reduction).**

$$\begin{aligned}\forall n , m \in \mathbb{N},\\(1 \le n) \Rightarrow\\(m \le n - 1) \Rightarrow\\\sum_{k \in \operatorname{range}(m + 1)} (4^{k} \cdot \operatorname{t}(2 \cdot n , 2 \cdot (n - k)) \cdot \operatorname{rat}(\operatorname{choose}(2 \cdot (n - k) - 1 , 2 \cdot (n - m - 1))) \cdot \operatorname{rat}(2 \cdot n \cdot (m - k) + k)) = \frac{4^{n} \cdot \operatorname{rat}(2 \cdot (n - m - 1) + 1)}{2} \cdot ((2 \cdot \operatorname{rat}(n) - 1) \cdot \operatorname{coeff}(F_{n} , 2 \cdot (n - m - 1) + 1) - \operatorname{coeff}(F_{n} , 2 \cdot (n - m - 1)))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/CentralFactorialParityIdentity.weighted_sum_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The upper coefficient index is l=2(n-m-1)+1. The reflected coefficient expansion and adjacent-binomial relation give the displayed scalar multiple.

**Theorem 1.12 (Weighted Vanishing Sum).**

$$\begin{aligned}\forall n , m \in \mathbb{N},\\(1 \le n) \Rightarrow\\(m \le n - 1) \Rightarrow\\\sum_{k \in \operatorname{range}(m + 1)} (4^{k} \cdot \operatorname{t}(2 \cdot n , 2 \cdot (n - k)) \cdot \operatorname{rat}(\operatorname{choose}(2 \cdot (n - k) - 1 , 2 \cdot (n - m - 1))) \cdot \operatorname{rat}(2 \cdot n \cdot (m - k) + k)) = 0\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/CentralFactorialParityIdentity.identity_441` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reflect the coefficient expansion, use the parity identity for its odd part, and apply the adjacent-binomial relation. The weighted sum is a scalar multiple of the vanishing adjacent-coefficient difference. The parity identity is a prerequisite on the live proof path, in consumer-to-prerequisite direction.

## References

- Truth anchor: `D5/S1/Recurrence/CentralFactorialParityIdentity.A`
- Truth anchor: `D5/S1/Recurrence/CentralFactorialParityIdentity.Cpoly`
- Truth anchor: `D5/S1/Recurrence/CentralFactorialParityIdentity.Cpoly_even`
- Truth anchor: `D5/S1/Recurrence/CentralFactorialParityIdentity.F`
- Truth anchor: `D5/S1/Recurrence/CentralFactorialParityIdentity.F_factorization`
- Truth anchor: `D5/S1/Recurrence/CentralFactorialParityIdentity.adjacent_coefficients`
- Truth anchor: `D5/S1/Recurrence/CentralFactorialParityIdentity.centralFactorial`
- Truth anchor: `D5/S1/Recurrence/CentralFactorialParityIdentity.choose_adjacent`
- Truth anchor: `D5/S1/Recurrence/CentralFactorialParityIdentity.half_shift`
- Truth anchor: `D5/S1/Recurrence/CentralFactorialParityIdentity.identity_427`
- Truth anchor: `D5/S1/Recurrence/CentralFactorialParityIdentity.identity_441`
- Truth anchor: `D5/S1/Recurrence/CentralFactorialParityIdentity.weighted_sum_reduction`
