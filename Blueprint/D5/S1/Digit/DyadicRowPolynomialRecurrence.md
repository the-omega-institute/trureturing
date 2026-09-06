# Dyadic Row Polynomials and Their Pascal Accumulator

## Abstract

Dyadic row recurrence and Pascal accumulator identities for OEIS A373183.

**Definition 1.1 (Polynomial difference operator).**

$$\forall P: \mathbb{Z}[X], \operatorname{D}(P) = X \cdot (\operatorname{comp}(P, X + 1) - (P))$$

*Formalization.* `D5/S1/Digit/DyadicRowPolynomialRecurrence.D` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D maps integer polynomials to integer polynomials. X is the polynomial indeterminate, comp(P,Q) means polynomial composition P(Q), and 1 is the constant integer polynomial. All polynomial identities below are in Z[X].

**Theorem 1.2 (Additivity).**

$$\forall P, Q: \mathbb{Z}[X], \operatorname{D}(P + Q) = \operatorname{D}(P) + \operatorname{D}(Q)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DyadicRowPolynomialRecurrence.D_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The defining difference distributes over addition. This companion is used by both induction arguments.

**Theorem 1.3 (The zero-index boundary identity).**

$$\operatorname{D}(X) = X$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DyadicRowPolynomialRecurrence.D_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This identity supplies the boundary at row zero in the even recurrence.

**Theorem 1.4 (Multiplication by the indeterminate).**

$$\forall P: \mathbb{Z}[X], \operatorname{D}(X \cdot P) = X \cdot P + (X + 1) \cdot \operatorname{D}(P)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DyadicRowPolynomialRecurrence.D_X_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The commutator is the odd-index step of the valuation descent and the polynomial form of the accumulator's Pascal step.

**Definition 1.5 (The independent dyadic row recursion).**

$$\forall n: \mathbb{N}, \operatorname{R}(n) = \operatorname{ite}(n = 0, X, \operatorname{ite}(\operatorname{mod}(n, 2) = 0, \operatorname{D}(\operatorname{R}(\operatorname{div}(n, 2))), X \cdot \operatorname{R}(\operatorname{div}(n, 2))))$$

*Formalization.* `D5/S1/Digit/DyadicRowPolynomialRecurrence.R` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

R : N -> Z[X] is defined by this well-founded recursion on n. div(n,2) denotes natural-number integer division, and mod(n,2) denotes the remainder. ite(c,a,b) returns a when c holds and b otherwise. The recurrence is transcribed from OEIS A373183 (Kurkov, 2024); Conjectures 1 and 9 are stated there as conjectures; the proofs are this repository's.

**Theorem 1.6 (Initial row).**

$$\operatorname{R}(0) = X$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DyadicRowPolynomialRecurrence.R_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The initial polynomial is X.

**Theorem 1.7 (Odd rows).**

$$\forall n: \mathbb{N}, \operatorname{R}(2 \cdot n + 1) = X \cdot \operatorname{R}(n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DyadicRowPolynomialRecurrence.R_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The odd-row clause holds for every natural n, including zero.

**Theorem 1.8 (Even rows).**

$$\forall n: \mathbb{N}, (0 < n) \implies \operatorname{R}(2 \cdot n) = X \cdot (\operatorname{comp}(\operatorname{R}(n), X + 1) - (\operatorname{R}(n)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DyadicRowPolynomialRecurrence.R_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive n this recurrence is transcribed from OEIS A373183 (Kurkov, 2024) as scope-matched context. Conjectures 1 and 9 are stated there as conjectures; the proofs are this repository's.

**Theorem 1.9 (The valuation recurrence).**

$$\forall n: \mathbb{N}, (0 < n) \implies \operatorname{R}(2 \cdot n) = \operatorname{R}(n) + \operatorname{R}(n - (2^{\operatorname{padicValNat}(2, n)})) + \operatorname{R}(2 \cdot n - (2^{\operatorname{padicValNat}(2, n)}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DyadicRowPolynomialRecurrence.conjecture1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is Conjecture 1 from OEIS A373183 (Kurkov, 2024), where it is stated as a conjecture; its proof is this repository's. For positive n, padicValNat(2,n) is v_2(n), the exponent of 2 dividing n. Both subtractions n-2^v and 2n-2^v are truncated natural-number subtraction. Strong induction descends along the binary recursion: the even case applies D to the lower-index identity, and the odd case uses the commutator.

**Definition 1.10 (Binary weight).**

$$\forall n: \mathbb{N}, \operatorname{wt}(n) = \operatorname{sum}(\operatorname{digits}(2, n))$$

*Formalization.* `D5/S1/Digit/DyadicRowPolynomialRecurrence.wt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

wt : N -> N is the sum of Mathlib's Nat.digits 2 n, the list of binary digits in least-significant-first order; digits(2,0) is empty.

**Theorem 1.11 (Even rows have zero constant coefficient).**

$$\forall k: \mathbb{N}, \operatorname{coeff}(\operatorname{R}(2 \cdot k), 0) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DyadicRowPolynomialRecurrence.R_coeff_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P=R(2k), this is the atom-named identity P(0)=0, expressed as its constant coefficient. The proof is this repository's.

**Theorem 1.12 (Even-row degree bound).**

$$\forall k: \mathbb{N}, \operatorname{natDegree}(\operatorname{R}(2 \cdot k)) \leq \operatorname{wt}(k) + 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DyadicRowPolynomialRecurrence.R_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P=R(2k) and d=wt(k)+1, this is the atom-named bound deg(P)<=d. The proof is this repository's.

**Definition 1.13 (Triangle coefficients).**

$$\forall n, q: \mathbb{N}, \operatorname{T}(n, q) = \operatorname{coeff}(\operatorname{R}(n), q)$$

*Formalization.* `D5/S1/Digit/DyadicRowPolynomialRecurrence.T` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

T : N -> N -> Z is defined by T(n,q)=(R(n)).coeff(q). Thus T(n,q) is the integer coefficient of X^q, including the zero coefficient q=0.

**Definition 1.14 (The independent coefficient accumulator).**

$$\begin{aligned}(\forall k, q: \mathbb{N}, \operatorname{e}(0, k, q) = 0)\\(\forall k, q: \mathbb{N}, \operatorname{e}(1, k, q) = \operatorname{ite}(q = 1, \operatorname{T}(2 \cdot k, \operatorname{wt}(k) + 1), 0))\\(\forall r, k, q: \mathbb{N}, \operatorname{e}(r + 2, k, q) = \operatorname{ite}(0 < q \land q \leq r + 2, \operatorname{e}(r + 1, k, q) + \operatorname{e}(r + 1, k, q - (1)) + \operatorname{ite}(r + 2 \leq \operatorname{wt}(k) + q, \operatorname{T}(2 \cdot k, \operatorname{wt}(k) + q + 1 - (r + 2)), 0), 0))\end{aligned}$$

*Formalization.* `D5/S1/Digit/DyadicRowPolynomialRecurrence.e` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

e : N -> N -> N -> Z is defined independently by these clauses, not by the target row formula. ite(c,a,b) means if c then a else b. Support takes priority outside 1<=q<=r. Every subtraction in q-1 and wt(k)+q+1-(r+2) is truncated natural-number subtraction. This is the accumulator transcribed from OEIS A373183 (Kurkov, 2024) as part of Conjecture 9; Conjectures 1 and 9 are stated there as conjectures; the proofs are this repository's.

**Theorem 1.15 (Support interval).**

$$\forall r, k, q: \mathbb{N}, (q = 0 \lor r < q) \implies \operatorname{e}(r, k, q) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DyadicRowPolynomialRecurrence.e_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The accumulator is zero at q=0 and above row r, equivalently outside [1,r].

**Theorem 1.16 (Initial accumulator entry).**

$$\forall k: \mathbb{N}, \operatorname{e}(1, k, 1) = \operatorname{T}(2 \cdot k, \operatorname{wt}(k) + 1)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DyadicRowPolynomialRecurrence.e_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sole supported entry at r=1 is the source coefficient T(2k,wt(k)+1).

**Theorem 1.17 (Pascal recurrence on the support).**

$$\forall r, k, q: \mathbb{N}, (2 \leq r) \implies (0 < q \land q \leq r) \implies \operatorname{e}(r, k, q) = \operatorname{e}(r - (1), k, q) + \operatorname{e}(r - (1), k, q - (1)) + \operatorname{ite}(r \leq \operatorname{wt}(k) + q, \operatorname{T}(2 \cdot k, \operatorname{wt}(k) + q + 1 - (r)), 0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DyadicRowPolynomialRecurrence.e_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For r>=2 and 1<=q<=r the two previous entries are supplemented by T(2k,wt(k)+q+1-r) when r<=wt(k)+q, and zero otherwise. The guard is equivalent to the source's integer inequality r-q<=wt(k). All subtractions r-1, q-1 and wt(k)+q+1-r in this display are natural-number subtraction.

**Theorem 1.18 (Independent binary row factorization).**

$$\forall m, k: \mathbb{N}, \operatorname{R}(2^{m + 1} \cdot (2 \cdot k + 1) - (2)) = \operatorname{D}(X^{m} \cdot \operatorname{R}(2 \cdot k))$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DyadicRowPolynomialRecurrence.R_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction through the odd-row clause gives the binary tail, then the even clause gives this factorization. The subtraction of 2 in the row index is natural-number subtraction.

**Definition 1.19 (Accumulator polynomial).**

$$\forall r, k: \mathbb{N}, \operatorname{E}(r, k) = \sum_{q \in \operatorname{range}(r + 1)} \operatorname{monomial}(q, \operatorname{e}(r, k, q))$$

*Formalization.* `D5/S1/Digit/DyadicRowPolynomialRecurrence.E` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

E : N -> N -> Z[X] is the finite sum over q in Finset.range(r+1), that is 0<=q<=r. monomial(q,a) is the integer polynomial a*X^q; this explicitly embeds the integer coefficient e(r,k,q) into Z[X].

**Theorem 1.20 (Accumulator at the degree bound).**

$$\forall k: \mathbb{N}, \operatorname{E}(\operatorname{wt}(k) + 1, k) = \operatorname{D}(\operatorname{R}(2 \cdot k))$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DyadicRowPolynomialRecurrence.E_at_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put P=R(2k) and d=wt(k)+1. The identities P.coeff(0)=0 and natDegree(P)<=d recover P at d and give E(d,k)=D(P).

**Theorem 1.21 (Accumulator after the degree bound).**

$$\forall m, k: \mathbb{N}, \operatorname{E}(\operatorname{wt}(k) + 1 + m, k) = \operatorname{D}(X^{m} \cdot \operatorname{R}(2 \cdot k))$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DyadicRowPolynomialRecurrence.E_after_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put P=R(2k) and d=wt(k)+1. The proof derives P.coeff(0)=0 and natDegree(P)<=d, identifies the accumulator with D of a truncated Horner polynomial, recovers P at d, and obtains X^m*P at d+m. In particular m=0 gives E(d,k)=D(P).

**Theorem 1.22 (The Pascal accumulator identity).**

$$\forall m, k, q: \mathbb{N}, (0 < q) \implies \operatorname{T}(2^{m + 1} \cdot (2 \cdot k + 1) - (2), q) = \operatorname{e}(m + \operatorname{wt}(k) + 1, k, q)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DyadicRowPolynomialRecurrence.conjecture9` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is Conjecture 9 from OEIS A373183 (Kurkov, 2024), where it is stated as a conjecture; its proof is this repository's. The subtraction of 2 in the row index is natural-number subtraction. Coefficient extraction from the row factorization and accumulator identity proves the whole statement. This proof is independent of conjecture1; both proofs share D_add, D_X and D_X_mul.

## References

- Truth anchor: `D5/S1/Digit/DyadicRowPolynomialRecurrence.D`
- Truth anchor: `D5/S1/Digit/DyadicRowPolynomialRecurrence.D_X`
- Truth anchor: `D5/S1/Digit/DyadicRowPolynomialRecurrence.D_X_mul`
- Truth anchor: `D5/S1/Digit/DyadicRowPolynomialRecurrence.D_add`
- Truth anchor: `D5/S1/Digit/DyadicRowPolynomialRecurrence.E`
- Truth anchor: `D5/S1/Digit/DyadicRowPolynomialRecurrence.E_after_degree`
- Truth anchor: `D5/S1/Digit/DyadicRowPolynomialRecurrence.E_at_degree`
- Truth anchor: `D5/S1/Digit/DyadicRowPolynomialRecurrence.R`
- Truth anchor: `D5/S1/Digit/DyadicRowPolynomialRecurrence.R_coeff_zero`
- Truth anchor: `D5/S1/Digit/DyadicRowPolynomialRecurrence.R_degree`
- Truth anchor: `D5/S1/Digit/DyadicRowPolynomialRecurrence.R_even`
- Truth anchor: `D5/S1/Digit/DyadicRowPolynomialRecurrence.R_factorization`
- Truth anchor: `D5/S1/Digit/DyadicRowPolynomialRecurrence.R_odd`
- Truth anchor: `D5/S1/Digit/DyadicRowPolynomialRecurrence.R_zero`
- Truth anchor: `D5/S1/Digit/DyadicRowPolynomialRecurrence.T`
- Truth anchor: `D5/S1/Digit/DyadicRowPolynomialRecurrence.conjecture1`
- Truth anchor: `D5/S1/Digit/DyadicRowPolynomialRecurrence.conjecture9`
- Truth anchor: `D5/S1/Digit/DyadicRowPolynomialRecurrence.e`
- Truth anchor: `D5/S1/Digit/DyadicRowPolynomialRecurrence.e_one`
- Truth anchor: `D5/S1/Digit/DyadicRowPolynomialRecurrence.e_recurrence`
- Truth anchor: `D5/S1/Digit/DyadicRowPolynomialRecurrence.e_support`
- Truth anchor: `D5/S1/Digit/DyadicRowPolynomialRecurrence.wt`
