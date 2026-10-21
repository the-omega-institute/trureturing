---
bibkey: lapiana2025graphquantummagicsquares
authors: Francesca La Piana
year: 2025
title: Graph Quantum Magic Squares and Free Spectrahedra
doi: 10.48550/arXiv.2512.08797
url: https://arxiv.org/abs/2512.08797v3
claim: Question 1.3 asks whether graph quantum permutation matrices generate all graph quantum magic squares; Section 4.1 names C5 as a candidate for strict containment.
strata_touched:
  - D5/S3/Quantum/LaPianaGraphQuantumMagicSquares
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2512.08797

Source: https://arxiv.org/abs/2512.08797v3

## Statements

Question 1.3, page 3: “Given a graph Γ, does the matrix convex hull of its quantum permutation matrices P^(Γ) generate all graph quantum magic squares? That is, mconv(P^(Γ)) = M^(Γ)?”

Definition 2.1, page 4: “A quantum magic square of external size n and internal size s is a block matrix” with “Aij ∈ Psds(ℂ),” “such that, for every i, j,” the displayed row and column sums equal Is. The displayed relations are Σk=1ⁿ Aik = Is and Σk=1ⁿ Akj = Is.

Definition 2.3, page 5: “We say that R is matrix convex if” the displayed normalized blockwise sums belong to Rt. The normalization is Σi Vi*Vi = It, and the new block matrix is Σi Vi*A^(i)Vi. “Here the conjugation acts blockwise” and “Equivalently, we say that R is closed under matrix-valued convex combinations.”

Definition 2.3, page 5: “For a subset S ⊆ Matn(Hers(ℂ)), the matrix convex hull of S, denoted as mconv(S), is the smallest matrix convex set containing S.”

Definition 3.1, page 8: “A quantum magic square X = (Xij)1≤i,j≤n ∈ Matn(Hers(ℂ)) is called a graph quantum magic square if” X(Is ⊗ AΓ) = (Is ⊗ AΓ)X. “This commutation condition can be written in terms of internal blocks as” Σk∼j Xik = Σk∼i Xkj “∀ i, j ∈ {1, . . . , n},” “where k ∼ j means that vertices k and j are adjacent in Γ.”

Definition 3.2, pages 8–9: “Let Γ be a finite graph with adjacency matrix AΓ, and let s ≥ 1. We define the following sets of graph quantum magic squares:” M^(Γ)s := { X ∈ M^(n)s | X(Is ⊗ AΓ) = (Is ⊗ AΓ)X } and P^(Γ)s := { X ∈ M^(Γ)s | Xij² = Xij = Xij* for all i, j }.

Section 4.1, page 20: “A natural class of candidates is vertex-transitive or symmetric graphs, such as the cycle C5, the Petersen graph, and, more generally, any k-regular graph with a large automorphism group.” The displayed conjecture is mconv(P^(Γ)) ⊊ M^(Γ) for various graphs Γ.

## Encoding and boundary

The external indices are `Fin n`, the internal indices are `Fin s`, positivity is `Matrix.PosSemidef`, and the conjugate transpose is `Matrix.conjTranspose`. Graph adjacency is `SimpleGraph.Adj`. The smallest matrix convex family is expressed by membership in every matrix convex family containing the original one. Natural-number sizes include the unique empty size-zero level; the separating square has internal size two. The graph in the settling proposition is `SimpleGraph.cycleGraph 5`.

The C5 strict-containment statement is a repository-derived answer to the source's question. It uses the block matrix with entries (1/25)[[5+a(i−j), b(i+j)], [b(i+j), 5−a(i−j)]], where a=(3,−3,0,0,0), b=(4,−4,0,0,0), and indices are modulo five. A decomposition into positive circulant and anti-circulant summands is obstructed by the distinct kernels of four rank-one blocks.

The universal odd-cycle extension, even cycles of size at least six, the Petersen graph and general vertex-transitive graphs are not concluded by this module. The source's C4 counterexample and free-spectrahedral results remain separate results. Completeness of the literature exclusion is ASSUMED-UNVERIFIED.
