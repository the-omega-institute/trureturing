# D-Bonacci Names

## Abstract

Boolean words avoiding d consecutive true digits form d-bonacci-sized layers.

The sequence uses the normalization D_d(0)=0 and D_d(1)=1. Its shifted initial layers satisfy D_d(Q+2)=2^Q for Q<d; after that point each term is the sum of its preceding d terms. A name is scanned with a finite true-run budget, reset by false and decreased by true.

**Theorem 1.1 (D-bonacci name layers have d-bonacci cardinality).**

$$\forall d \in N,\; \forall Q \in N,\; \operatorname{card}\left(\operatorname{DBonacciName}\left(d, Q\right)\right) = \operatorname{D}\left(d, Q + 2\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/Names.dbonacci_name_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For Q<d every Boolean word is admissible, giving 2^Q names. For Q>=d, splitting at the first false among the initial d positions gives the d preceding name layers. Strong induction identifies this recurrence with D_d(Q+2), fixing the offset at plus two.

The compiled small-case table covers d=2,3,4 and Q=0 through 4. Its rows are 1,2,3,5,8; 1,2,4,7,13; and 1,2,4,8,15.

Pinned Mathlib, Loogle, and LeanSearch were queried for k-bonacci, generalized Fibonacci, LinearRecurrence, and binary strings avoiding runs. Mathlib supplies Nat.fib and the generic LinearRecurrence structure, but no exact d-bonacci sequence or avoiding-run count theorem was found, so the finite-state decomposition is proved here.

**Theorem 1.2 (Order-three d-bonacci is the frozen Tribonacci sequence).**

$$\forall n \in N,\; \operatorname{D}\left(3, n\right) = \operatorname{T}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/Names.dbonacci_three_eq_tribonacci` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The order-three recurrence and the first three values agree with the existing Tribonacci module. Strong induction therefore proves pointwise equality without redefining or modifying the frozen specialization.

**Theorem 1.3 (Order-two d-bonacci is mathlib Fibonacci).**

$$\forall n \in N,\; \operatorname{D}\left(2, n\right) = \operatorname{Fib}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/Names.dbonacci_two_eq_fib` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At order two the recurrence is D_2(n+2)=D_2(n)+D_2(n+1), with initial values zero and one. The proof applies mathlib's Nat.fib_add_two after establishing the general sequence's two-term equation.

## References

- Truth anchor: `D5/S0/Tower/DBonacci/Names.dbonacci_name_card`
- Truth anchor: `D5/S0/Tower/DBonacci/Names.dbonacci_three_eq_tribonacci`
- Truth anchor: `D5/S0/Tower/DBonacci/Names.dbonacci_two_eq_fib`
- Dependency: [D5/S0/Tower/Tribonacci/Names](../Tribonacci/Names.md)
