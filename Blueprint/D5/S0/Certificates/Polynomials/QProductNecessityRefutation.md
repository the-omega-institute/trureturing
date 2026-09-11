# A counterexample to Conjecture 5.4's necessity clause

## Abstract

The necessity clause of Conjecture 5.4 is false: six factors [2]_q and one factor [2]_(q^3) give a unimodal polynomial outside the proposed condition.

Connelly, Ito, Martinez, Shevchenko and Yang's arXiv:2605.12822v1, section 5.2, asserts that when k is at most three or r is at most three, unimodality forces either divisibility of some a_i by r or the bound b at most one plus the sum of the floors a_i/r. The formal claim retains all positive-integer parameters, both alternatives, and the stated lower bounds on r and k. Corollary 4.3 explicitly says 'for some', which fixes the reading of the divisibility quantifier in the conjecture.

**Theorem 1.1 (The universal necessity assertion is false).**

Lean statement: `D5/S0/Certificates/Polynomials/QProductNecessityRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Polynomials/QProductNecessityRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Brendan B. Connelly; Ezekiel Ito; Thomas C. Martinez; Olha Shevchenko; Kacey Yang (2026). *Unimodality of q-Fibonomial coefficients for small cases*. URL: <https://arxiv.org/html/2605.12822v1>.

*Commentary.*

Take r=3, k=6, a_i=2 for every index, and b=2. The actual geometric product is (1+q)^6(1+q^3). Its coefficients, including all internal positions, are 1, 6, 15, 21, 21, 21, 21, 15, 6, 1. They rise weakly to index three and fall weakly thereafter. Mathlib's binomial coefficient and polynomial shift identities give these values and the zero tail. Yet three divides none of the entries, and the proposed upper bound on b is one. The r at most three premise holds.

The paper reports checking only k at most five; this witness has k=6. Its following example has k=r=4 and therefore misses the restricted necessity premise. The present result concerns the necessity clause alone. The sufficiency clause and a classification of all such products are not asserted here.

## References

- Truth anchor: `D5/S0/Certificates/Polynomials/QProductNecessityRefutation.result`
