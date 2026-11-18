# Dyadic blocks of the extended Stirling array

## Abstract

The literal rational extended Stirling array satisfies Kurkov's complete dyadic block identity.

Mikhail Kurkov's OEIS A358612 defines extended Stirling numbers through the binary expansion of the row index. All row and column indices below are natural numbers, including zero. Array values and their arithmetic are rational. Nat.div(a,b) is natural-number quotient, and Nat.sub(a,b)=max(a-b,0) is truncated natural subtraction. The notation (k:Q) denotes the canonical rational image of k; Q and N denote the rational and natural numbers. ite(P,a,b) denotes a if P holds and b otherwise. These index operations are distinct from rational subtraction and division.

**Definition 1.1 (The literal rational recursion).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{T}\left(n, k\right) = \operatorname{ite}\left(k = 0, 0, \operatorname{ite}\left(k = 1, 1, \operatorname{ite}\left(n = 0, \operatorname{ite}\left(k = 2, 1, 0\right), ((k:\mathbb{Q}) \cdot \operatorname{T}\left(\operatorname{Nat.div}\left(n, 2\right), k\right) + \operatorname{T}\left(\operatorname{Nat.div}\left(n, 2\right), \operatorname{Nat.sub}\left(k, 1\right)\right)) - \operatorname{ite}\left(n \bmod 2 = 0, \frac{(\operatorname{T}\left(n, \operatorname{Nat.sub}\left(k, 1\right)\right) + \operatorname{T}\left(\operatorname{Nat.div}\left(n, 2\right), \operatorname{Nat.sub}\left(k, 1\right)\right))}{((k:\mathbb{Q}) - 1)}, 0\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/DyadicExtendedStirlingBlock.T` (`✓ std3`).

*Citation.* Mikhail Kurkov (2024). *OEIS A358612: extended Stirling numbers from binary row indices*. URL: <https://oeis.org/A358612>.

*Commentary.*

The map T:N x N -> Q is defined by lexicographic recursion on (n,k), decreasing the row before the column. Column zero is separately set to zero. Every row has T(n,1)=1; the initial row has T(0,2)=1 and T(0,k)=0 for k>=3. For m>=0 and k>=2 the odd recursion reads T(2m+1,k)=k*T(m,k)+T(m,k-1). For m>=1 and k>=2 the even recursion subtracts (T(2m,k-1)+T(m,k-1))/(k-1) from k*T(m,k)+T(m,k-1). Here the coefficients k and k-1 and the displayed division are rational. Recursive column indices use Nat.sub. Every column used by these positive-domain recurrences is at least one, so their values are independent of the zero-column convention. The definition uses the source scalar recursion and initial values, without assuming the block identity.

**Definition 1.2 (The dyadic valuation).**

$$\forall n \in \mathbb{N},\; \operatorname{g}\left(n\right) = \operatorname{padicValNat}\left(2, n\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/DyadicExtendedStirlingBlock.g` (`✓ std3`).

*Citation.* Mikhail Kurkov (2024). *OEIS A358612: extended Stirling numbers from binary row indices*. URL: <https://oeis.org/A358612>.

*Commentary.*

The map g:N -> N is padicValNat 2. For n>0 it is the exponent of the highest power of two dividing n, OEIS A007814(n). The natural-valued convention at zero is g(0)=0.

**Definition 1.3 (The natural parent index).**

$$\forall n \in \mathbb{N},\; \operatorname{h}\left(n\right) = \operatorname{Nat.div}\left(\operatorname{Nat.sub}\left(\operatorname{Nat.div}\left(n, (2)^{\operatorname{g}\left(n\right)}\right), 1\right), 2\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/DyadicExtendedStirlingBlock.h` (`✓ std3`).

*Citation.* Mikhail Kurkov (2024). *OEIS A358612: extended Stirling numbers from binary row indices*. URL: <https://oeis.org/A358612>.

*Commentary.*

The map h:N -> N first takes the natural quotient n/2^g(n), then subtracts one with natural monus, then takes the natural quotient by two. In particular h(0)=0. For positive n the quotient by 2^g(n) is exact and odd, and n=2^g(n)*(2*h(n)+1). Thus h(n)=A025480(n-1) on the source domain; no integer-floor expression with a negative numerator is used at zero.

**Theorem 1.4 (Exact positive-row decomposition).**

$$\forall n \in \mathbb{N},\; (0 < n) \Rightarrow (n = (2)^{\operatorname{g}\left(n\right)} \cdot \left(2 \cdot \operatorname{h}\left(n\right) + 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/DyadicExtendedStirlingBlock.dyadic_index` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mikhail Kurkov (2024). *OEIS A358612: extended Stirling numbers from binary row indices*. URL: <https://oeis.org/A358612>.

*Commentary.*

For every positive natural n, n=2^g(n)*(2*h(n)+1). The proof uses the exact power-of-two valuation and odd quotient. This source-owner helper is consumed by the block theorem and by the row-edge induction; no claim is made at zero.

**Theorem 1.5 (The complete dyadic block identity).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; (1 \le n) \Rightarrow ((2 \le k) \Rightarrow (\operatorname{T}\left(n, k\right) = ((k:\mathbb{Q}) - 1)^{\operatorname{g}\left(n\right)} \cdot \operatorname{T}\left(\operatorname{h}\left(n\right), \operatorname{Nat.sub}\left(k, 1\right)\right) + ((k:\mathbb{Q}))^{\operatorname{g}\left(n\right) + 1} \cdot \operatorname{T}\left(\operatorname{h}\left(n\right), k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/DyadicExtendedStirlingBlock.dyadic_extended_stirling_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mikhail Kurkov (2024). *OEIS A358612: extended Stirling numbers from binary row indices*. URL: <https://oeis.org/A358612>.

*Commentary.*

For every n>=1 and k>=2, with no upper bound on either index, this is Kurkov's final FORMULA conjecture in A358612. All powers have natural exponents and rational bases. The base (k:Q)-1 is parenthesized; the index Nat.sub(k,1) is a natural number. The proof first establishes the same identity at row 2^r*(2*h+1) for all natural r and h by induction on r, with an inner induction on k in the even step. The case k=2 uses the constant first column, and the case r=0 uses the odd recursion. The valuation decomposition then identifies the row with n. This includes g(n)=0 and h(n)=0. The proof is a derivation in this repository; the assertion and its attribution are Kurkov's. Integrality, row-edge values and the separate transform conjectures are outside this statement.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/DyadicExtendedStirlingBlock.T`
- Truth anchor: `D5/S1/Recurrence/Parity/DyadicExtendedStirlingBlock.dyadic_extended_stirling_block`
- Truth anchor: `D5/S1/Recurrence/Parity/DyadicExtendedStirlingBlock.dyadic_index`
- Truth anchor: `D5/S1/Recurrence/Parity/DyadicExtendedStirlingBlock.g`
- Truth anchor: `D5/S1/Recurrence/Parity/DyadicExtendedStirlingBlock.h`
