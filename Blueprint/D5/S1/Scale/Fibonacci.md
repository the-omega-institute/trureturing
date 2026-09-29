# Golden Powers and Fibonacci Coordinates

## Abstract

Powers of the golden generator have consecutive Fibonacci coordinates.

Write a golden integer as a pair (a,b), representing a+b phi, where phi squared equals phi plus one. The Fibonacci sequence starts with F_0=0 and F_1=1.

**Theorem 1.1 (Coordinates of positive powers).**

$$\forall n\in\mathbb{N},\varphi^{n+1}=(F_n,F_{n+1})$$

*Proof.* Machine-checked in Lean as `D5/S1/Scale/Fibonacci.golden_phi_pow_eq_fib_pair` (`✓ std3`). ∎

*Citation.* Thomas Koshy (2001). *Fibonacci and Lucas Numbers with Applications*. DOI: [10.1002/9781118033067](https://doi.org/10.1002/9781118033067).

*Commentary.*

For every natural n, the two integral coordinates of phi^(n+1) are F_n and F_(n+1). Multiplication by phi sends (a,b) to (b,a+b).

**Theorem 1.2 (Cassini identity).**

$$\forall n\in\mathbb{N},F_nF_{n+2}-F_{n+1}^2=(-1)^{n+1}$$

*Proof.* Machine-checked in Lean as `D5/S1/Scale/Fibonacci.fib_cassini_from_golden_norm` (`✓ std3`). ∎

*Citation.* Thomas Koshy (2001). *Fibonacci and Lucas Numbers with Applications*. DOI: [10.1002/9781118033067](https://doi.org/10.1002/9781118033067).

*Commentary.*

Taking the integer norm of the coordinate identity gives Cassini's identity. The norm of phi is minus one.

## References

- Truth anchor: `D5/S1/Scale/Fibonacci.fib_cassini_from_golden_norm`
- Truth anchor: `D5/S1/Scale/Fibonacci.golden_phi_pow_eq_fib_pair`
- Dependency: [D5/S0/Carrier/Units](../../S0/Carrier/Units.md)
