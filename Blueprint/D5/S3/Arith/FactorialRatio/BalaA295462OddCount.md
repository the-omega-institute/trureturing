# Counting and enumerating the odd values of A295462

## Abstract

The odd values of A295462 below 2^m are counted by c_m=c_{m-1}+c_{m-4}, and their indices are enumerated block by block.

**Definition 1.1 (Odd values).**

Lean statement: `D5/S3/Arith/FactorialRatio/BalaA295462OddCount.oddValue`

*Formalization.* `D5/S3/Arith/FactorialRatio/BalaA295462OddCount.oddValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

oddValue n states that a(n)=(15n)!(2n)!/((10n)!(6n)!n!) equals an odd natural number.

**Definition 1.2 (Counts below powers of two).**

Lean statement: `D5/S3/Arith/FactorialRatio/BalaA295462OddCount.c`

*Formalization.* `D5/S3/Arith/FactorialRatio/BalaA295462OddCount.c` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

c m is the number of n with 0≤n<2^m for which a(n) is odd.

**Definition 1.3 (Increasing enumeration).**

Lean statement: `D5/S3/Arith/FactorialRatio/BalaA295462OddCount.u`

*Formalization.* `D5/S3/Arith/FactorialRatio/BalaA295462OddCount.u` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

u j is the j-th index n, counted from zero, for which a(n) is odd.

**Theorem 1.4 (The count recurrence).**

Lean statement: `D5/S3/Arith/FactorialRatio/BalaA295462OddCount.count_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/BalaA295462OddCount.count_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

c_0=1, c_1=2, c_2=3, c_3=4, and c_m=c_{m−1}+c_{m−4} for every m≥4. Since a(n) is odd exactly when any two occupied binary positions of n differ by at least four, c counts such n below 2^m. For y<2^e the number 2^e+y has the binary positions of y together with e; it is four-separated exactly when y is and every position of y is at most e−4, that is y<2^(e−3) with truncated subtraction. Splitting the n<2^(e+1) by the position e gives c_{e+1}=c_e+c_{e−3} for every e≥0; for e≤2 the second term is c_0=1.

**Theorem 1.5 (Block enumeration).**

Lean statement: `D5/S3/Arith/FactorialRatio/BalaA295462OddCount.enumeration`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/BalaA295462OddCount.enumeration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

u_0=0, and for every j>0 there is exactly one e with c_e≤j<c_{e+1}; for it, u_j=2^e+u_{j−c_e}. Existence and uniqueness follow because c is strictly increasing and unbounded with c_0=1. Write i=j−c_e<c_{e−3}; then y=u_i<2^(e−3), so 2^e+y is four-separated, and exactly c_e+i such indices lie below it. Hence it is the j-th index.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/BalaA295462OddCount.c`
- Truth anchor: `D5/S3/Arith/FactorialRatio/BalaA295462OddCount.count_recurrence`
- Truth anchor: `D5/S3/Arith/FactorialRatio/BalaA295462OddCount.enumeration`
- Truth anchor: `D5/S3/Arith/FactorialRatio/BalaA295462OddCount.oddValue`
- Truth anchor: `D5/S3/Arith/FactorialRatio/BalaA295462OddCount.u`
- Dependency: [D5/S3/Arith/FactorialRatio/BalaA295462Parity](BalaA295462Parity.md)
