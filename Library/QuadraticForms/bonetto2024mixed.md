---
bibkey: bonetto2024mixed
authors: Riccardo Bonetto; Hildeberto Jardón Kojakhmetov
year: 2024
title: "On the Eigenvalues of Graphs with Mixed Algebraic Structure"
doi: null
url: https://arxiv.org/html/2408.00487v1
claim: "Definition 3 assigns the matrix M(ε)=L_G+ε A_H to a disjoint spanning edge partition of a finite simple graph, for ε>0. Definitions 7 and 8 count real eigenvalues with multiplicity and define signature as Nplus minus Nminus. Section 3, Conjecture 1 asks whether this signature is nonincreasing in ε."
strata_touched:
  - D5/S3/Combinatorics/SpectralGraph/BonettoSignature
license: citation-only
triage: anchor
---

# Mixed Laplacian and adjacency structure

The paper considers a finite simple undirected graph F and spanning
subgraphs G,H with disjoint edge sets whose union is the edge set of F.
Definitions 1 and 2 use the ordinary 0/1 adjacency matrix and the
combinatorial Laplacian D−A. Definition 3 sets

$$M(u)=L_G+uA_H,\qquad u>0.$$

Remark 1 states that these are real symmetric matrices with a complete
orthogonal eigenbasis. Definition 7 counts negative, zero and positive
eigenvalues with multiplicity. Definition 8 defines

$$s(Q)=N_+(Q)-N_-(Q).$$

Conjecture 1 in Section 3 reads:

> The signature of the matrix M(ε) is a monotonic decreasing function of ε.

Here decreasing is interpreted as nonincreasing: the accompanying step
plots include constant intervals. The quantified assertion is

$$0<s\le t\quad\Longrightarrow\quad s(M(t))\le s(M(s)).$$

No invertibility, connectivity, simple spectrum or small-parameter
restriction is imposed on the conjecture. Singular matrices and zero
eigenvalues remain part of its scope. The formal statement also includes
the empty vertex type. The paragraph following the conjecture proposes
the corresponding assertion for A+uB with A real symmetric positive
semidefinite and B real symmetric. The subsequent limiting-signature
and transition-count claims are separate assertions.

## Verified locator

- URL: https://arxiv.org/html/2408.00487v1 — Definitions 1–3 and Remark 1
  in Section 2; Definitions 7–8 and Remark 2; Section 3, Conjecture 1 and
  its following discussion and plots; Section 4, Outlook. The primary
  HTML was read directly. Its 310776 bytes have SHA-256
  `49a537fe5a5f96ce679a8f487f0e9aa4053e2f7af7e46c79dcc83c12774b4b88`.

The inspected arXiv version history lists only v1, submitted 1 August
2024. That source labels the assertion Conjecture 1, and its outlook
asks for a proof or further understanding. Bounded title, author and
content searches supplied no later exact settlement; inaccessible and
unindexed sources remain outside that finding. This is not an assertion
of worldwide priority or exhaustive literature coverage. The matrix
definitions and the conjecture are source material; the formal
positive-subspace assembly is repository-derived from existing inertia
results.
