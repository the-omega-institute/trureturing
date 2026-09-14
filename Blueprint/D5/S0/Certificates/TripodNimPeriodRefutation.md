# Tripod Nim: the printed period assertion

## Abstract

A periodic orbit of D(3,10) has least period 264, which does not divide 3280.

**Definition 1.1 (The transition of the three-row system).**

Lean statement: `D5/S0/Certificates/TripodNimPeriodRefutation.transition`

*Formalization.* `D5/S0/Certificates/TripodNimPeriodRefutation.transition` (`✓ std3`).

*Citation.* Aidan Hennessey (2024). *Tree and Tripod Nim*. DOI: [10.48550/arXiv.2401.07943](https://doi.org/10.48550/arXiv.2401.07943).

*Commentary.*

Section 9.3 uses three Boolean rows with 2n+3 columns. Columns are numbered from the left, and rows are listed from bottom to top. A step shifts left, appends zeros, and inserts one into each row whose departing bit was zero. Each insertion uses the leftmost zero outside the first n columns and outside the columns already chosen by this step. An unavailable insertion gives an absorbing undefined state, so a returning present board has only defined steps.

**Definition 1.2 (Conjecture 2 as printed).**

Lean statement: `D5/S0/Certificates/TripodNimPeriodRefutation.claim`

*Formalization.* `D5/S0/Certificates/TripodNimPeriodRefutation.claim` (`✓ std3`).

*Citation.* Aidan Hennessey (2024). *Tree and Tripod Nim*. DOI: [10.48550/arXiv.2401.07943](https://doi.org/10.48550/arXiv.2401.07943).

*Commentary.*

Conjecture 2 on printed page 30 of arXiv:2401.07943v1 says that every periodic orbit of D(3,n) has a period dividing 2(4n)(4n+1). The definition quantifies over all three-row periodic boards of the transition and uses Mathlib's minimalPeriod. Requiring the least period to divide the displayed number is equivalent to the existence of such a period. Remark 9.2 reports confirmation for n at most nine.

**Theorem 1.3 (A period of 264 at n=10).**

Lean statement: `D5/S0/Certificates/TripodNimPeriodRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/TripodNimPeriodRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Aidan Hennessey (2024). *Tree and Tripod Nim*. DOI: [10.48550/arXiv.2401.07943](https://doi.org/10.48550/arXiv.2401.07943).

*Commentary.*

With bit zero representing the leftmost column, the rows of the chosen board encode 1, 2047 and 2042 from bottom to top. The word evaluator returns to this board after 264 steps, and fails to return after 24, 88 and 132 steps. Decoding commutes with each transition and is injective, which transfers both return and nonreturn statements to the Boolean board semantics.

Every proper divisor of 264 divides 132, 88 or 24, so the least period is exactly 264. At n=10 the printed expression is 3280, and 3280 equals 12 times 264 plus 112. This contradicts exactly the printed Conjecture 2. No initial-state reachability assertion is needed. No priority for the example, no conclusion about other results in the paper, and no corrected formula are claimed.

## References

- Truth anchor: `D5/S0/Certificates/TripodNimPeriodRefutation.claim`
- Truth anchor: `D5/S0/Certificates/TripodNimPeriodRefutation.result`
- Truth anchor: `D5/S0/Certificates/TripodNimPeriodRefutation.transition`
