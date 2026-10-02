---
slug: beluhov-2026-conjecture-3-dimension-refutation
bibkey: beluhov2026diamond
doi: null
url: https://arxiv.org/abs/2602.24239v2
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.result
---

# Refutation of Beluhov's invariant-kernel dimension conjecture at type (1,3,6)

## Problem

Nikolai Beluhov, *Diamond Determinants and Somos Sequences*, arXiv:2602.24239v2, Section 10, page 24, states:

> For every proper type 𝐧 of order n, it holds that dim Ω⊠ = ⌊n/2⌋.

The formal claim uses the paper's stated parity-only gauge space, the rational-function field in three independent coefficients, and the kernel of the displayed operator over the constrained monomial subspace.

## Motivation

Issue #11548 preregisters this published named conjecture as an unsettled Tier-1 problem. The settlement studies the proper type (1,3,6), whose order is 10, and tests the predicted dimension 5 over the independent-parameter field.

The scope is the parity-only gauge reading stated in the paper. The larger type-dependent gauge space obtained by imposing only the three nonzero recurrence terms is a separate interpretation and is excluded from this resolution.

## Gap

The source reports direct checks through proper types of order 9 and leaves the universal assertion open. The bounded literature and repository searches recorded in issue #11548 found no proof or refutation of Conjecture 3. Those searches do not establish exhaustive literature coverage or publication priority.

## Route

The module defines the coefficient field, Gale--Robinson types and properness, the parity-gauge admissible monomials, the constrained subspace, the homogenized substitution, the linear operator, and its restricted kernel. For type (1,3,6), it constructs six explicit polynomials H₀,…,H₅ in the constrained subspace and verifies that each is in the kernel. Six coefficient functionals have diagonal values 1, b, b², c, bc², bc, which are nonzero in the rational-function field, so the six kernel elements are independent. The finite monomial span supplies finite dimensionality, giving a kernel dimension at least 6 while the claim predicts 5.

## Falsifier

A proof of the universal claim with the same parity-only gauge definitions would falsify this refutation. At the certificate level, failure of any six kernel identities, failure of the six coefficient equations, or failure of the independence certificate would invalidate the lower bound. The result does not assert a matching upper bound.

## Evidence

- Lean module: `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.lean`.
- The public settlement theorem is `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.result : ¬ claim`.
- The theorem is kernel-checked with the standard axioms `[propext, Classical.choice, Quot.sound]`.
- The freeze event anchors the declaration set; its prerequisite list is empty because the module imports no D5 module.
- The Scribe mirror and emitted Markdown display the same parity-only formulas, including `Finsupp.equivFunOnFinite.symm` and `Fin.mk`.

## Triage

`theorem`; resolution `refuted` under the parity-only gauge reading. The result proves a strict lower bound of six for the type-(1,3,6) restricted kernel, which contradicts the conjectured value five. The source's reported lower-order checks and its other conjectures survive. The full type-dependent gauge interpretation, an exact dimension at type (1,3,6), a corrected universal formula, and consequences for other types remain open.

### What the settlement shows

- **Proved in this module:** six independent elements lie in the parity-gauge restricted kernel for the proper type (1,3,6), so its dimension is at least 6 and Conjecture 3 is false.
- **Proved mechanism:** the six kernel identities and the diagonal coefficient certificate force independence over the rational-function field; the contradiction is the strict lower bound 6 versus the predicted 5.
- **Computed:** type (1,3,6) has order 10 and the conjectured value is 10/2 = 5.
- **Open:** whether the exact parity-gauge dimension is 6 or larger, and how the dimension behaves for neighboring proper types.
- **Open:** the dimension under the larger type-dependent gauge space and any corrected universal statement. The source's other conjectures are outside this theorem.

## ASSUMED-UNVERIFIED

The literature search is bounded by the sources and queries recorded in issue #11548; it does not establish exhaustive absence of a later settlement. The identification of the paper's parity-only gauge reading with the formal encoding is documented in the Library note and is not itself a kernel theorem.
