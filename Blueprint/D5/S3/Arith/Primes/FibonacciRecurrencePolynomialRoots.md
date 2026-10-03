# Exact Complex Roots of the Odd Recurrence Polynomial

## Abstract

The complex root multiset of every odd-index plus-recurrence polynomial is given by a simple cosine formula.

**Theorem 1.1 (Odd recurrence root multiset).**

Lean statement: `D5/S3/Arith/Primes/FibonacciRecurrencePolynomialRoots.odd_recurrence_polynomial_root_multiset`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/FibonacciRecurrencePolynomialRoots.odd_recurrence_polynomial_root_multiset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural r, after mapping the integer recurrence polynomial at index 2r+1 into the complex polynomial ring, its root multiset is the list indexed by 0 <= k < 2r whose kth entry is -2 times the imaginary unit times cos((k+1) pi/(2r+1)). The indexing records each root with its multiplicity.

## References

- Truth anchor: `D5/S3/Arith/Primes/FibonacciRecurrencePolynomialRoots.odd_recurrence_polynomial_root_multiset`
- Dependency: [D5/S3/Arith/Primes/FibonacciRecurrencePolynomialChebyshev](FibonacciRecurrencePolynomialChebyshev.md)
