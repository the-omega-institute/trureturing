# Cubic Probe Fourier Budget

## Abstract

Split and nonsplit restrictions have unequal normalized Fourier costs for the same exact period-forcing target.

**Theorem 1.1 (Sharp cubic Fourier budget for finite-horizon period forcing).**

Lean statement: `D5/S3/Arith/Primes/CubicProbeFourierBudget.cubic_fourier_budget_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/CubicProbeFourierBudget.cubic_fourier_budget_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive horizon P, prescribe split and nonsplit observations at disjoint sites from zero through P. The prescription forces every compatible binary signal to have no positive period at most P. Such a prescription with the explicit normalized cubic coefficient tensor's absolute mass at most M exists exactly when there are counts a and b with a times b at least P minus floor(P/2) and 3 to the a times 2 to the b at most M.

The unweighted nonsimply-bordered partial-word geometry is due to Blanchet-Sadri, Allen, Byrum and Mercas (LATA 2009, Theorem 1, DOI 10.1007/978-3-642-00982-2_15). Here the two weights come from the actual cyclic cubic identity filter and its complement, rather than assigning one cost to either mark.

The result is a rational coefficient-table and combinatorial design theorem for independent cubic labels. It does not assert Galois independence, a GRH explicit formula or prime bound, or the WSS factorization conjecture.

## References

- Truth anchor: `D5/S3/Arith/Primes/CubicProbeFourierBudget.cubic_fourier_budget_iff`
