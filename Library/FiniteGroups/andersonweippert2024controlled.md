---
bibkey: andersonweippert2024controlled
authors: J. T. Anderson and M. Weippert
year: 2024
title: Controlled Gates in the Clifford Hierarchy
doi: 10.48550/arXiv.2410.04711
url: https://arxiv.org/abs/2410.04711v3
claim: "Section 4 conjectures that a controlled qudit gate in the Clifford hierarchy has target order d^m for a nonnegative integer m."
strata_touched:
  - D5/S3/Arith/Primes/CyclicDifferencePrimeContent
  - D5/S3/Quantum/Algebra/WeylCliffordDescent
  - D5/S3/Quantum/Algebra/AndersonWeippertQuditControlledOrder
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2410.04711

Source: https://arxiv.org/abs/2410.04711v3

Section 4, printed page 7, states:

> It is tempting to conjecture for the qudit case that C(U) is in the Clifford Hierarchy only if U is order d^m where d is the local qudit dimension and m is a non-negative integer. We leave this as an open problem.

Section 1.1, printed page 2, defines:

> We will write C(U) = |0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U where the control is on the left side of the tensor product.

Section 2, printed page 2, describes the first hierarchy level:

> The elements form a group and consist of Pauli strings i.e. tensor products of single-qubit Pauli matrices times a U (1) phase (usually restricted to i^k or ±1).

> The details of this phase are not important here and any of these definitions of CH1 will suffice for our proofs below.

Equation (1), printed page 1, states:

> The n-qubit Clifford Hierarchy [1, 7] is recursively defined as CHk ≡ {U |U P U † ⊆ CHk−1 , ∀P ∈ Pn } with the first level (k = 1) defined as CH1 ≡ Pn , the n-qubit Pauli group.

The mathematical encoding fixes prime dimension p and n target coordinates,
with basis index type Fin n → ZMod p. The control coordinate is zero, the
operator U occupies control block one, and every other control block is the
identity. Pauli operators have arbitrary complex phase of norm one. Level
zero is empty; membership at some natural index means a finite hierarchy
level. The order is multiplicative matrix order, including the global phase.
The source's block-size description corresponds to n = 1; the theorem also
allows n = 0 and arbitrary larger n.

Repeated commutators with the control shift reach the identity. Their block
exponents are successive cyclic differences of the indicator of residue one.
The gcd of their absolute coefficients is nonzero and has no prime divisor
other than p. The target order divides that gcd. This is the repository's
proof of the conjectured necessity, rather than a theorem attributed to the
paper. The converse, the least level and other control patterns remain open.

The convention experiment is in
https://github.com/the-omega-institute/trureturing-experiments at commit
45ec3cd6e4ce67eca8b99d16c6bf5d692d8a3765, file
`docs/reports/anderson-weippert-2024-qudit-controlled-order/check.py`, SHA-256
`667a533e45d84e2260201ea2820e78bf279081567bb731d24804b99b847a7f0f`.
It exits 0 on its finite qubit and qutrit checks. Those computations test
conventions and bounded levels; they do not prove the universal theorem.

The literature screen is recorded at
https://github.com/the-omega-institute/trureturing/issues/19835.
Its completeness is ASSUMED-UNVERIFIED; the cited dissertation was not read.
