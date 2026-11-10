---
bibkey: saaltink2025qtransversals
authors: M. Saaltink
year: 2025
title: A theory of q-transversals
doi: 10.48550/arXiv.2503.12201
url: https://arxiv.org/abs/2503.12201v1
claim: "Conjecture 3. All q-transversal matroids are representable."
strata_touched:
  - D5/S3/Combinatorics/Matroids/QTransversalRepresentability
license: citation-only
triage: anchor
---

# Saaltink, q-transversals

## Verified locator

DOI: 10.48550/arXiv.2503.12201

Source: https://arxiv.org/abs/2503.12201v1

Section 4.2, page 14: “Conjecture 3. All q-transversal matroids are representable.”

Definition 14, page 8: “Let a vector space V be given, together with a family X = (X₁, …, X_n) of subspaces of V.” “A partial q-transversal is a dimension n subspace T where every vector basis of T is a partial avoiding transversal of X.” Theorems 15 and 18 treat partial q-transversals in all dimensions. The encoding therefore allows every subspace dimension. An avoiding injection assigns distinct family indices to basis vectors, each outside its assigned subspace.

Theorem 15, page 8: “Given a family X = (X_i : i ∈ I) where each X_i is a subspace of V, the set of partial q-transversals of X form the independent subspaces of a q-matroid.” The rank is the largest dimension of an independent subspace contained in the argument.

Section 3.2, page 7: “Given some n × m matrix G over a field K extending F_q, we can define the q-matroid represented by G as follows: if a subspace of F_q^m is the row space of matrix X, then its rank in the matroid is the rank of matrix G Xᵀ.” The Lean columns are the basis vectors of the argument subspace, mapped to K coordinatewise.

The representation theorem handles an arbitrary finite field and an arbitrary finite family of subspaces. It obtains one finite extension and one matrix for all argument subspaces simultaneously. The proof does not assert the sharper product formula for the extension degree. The coordinate-family construction of Theorem 24 is a special case of the conclusion. Conjectures 1 and 2 are separate questions.

The literature screen on issue #19965, including arXiv:2603.13550v1, did not identify an unrestricted representation theorem. Its completeness is ASSUMED-UNVERIFIED.
