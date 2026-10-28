---
bibkey: chendey2023orthostochastic
authors: Justin Chen; Papri Dey
year: 2023
title: "The 4 × 4 orthostochastic variety"
doi: 10.1080/10586458.2021.1982427
url: https://arxiv.org/abs/2001.10691
claim: "Question 5 asks whether the naive equations define the orthostochastic variety inside the Birkhoff polytope; Proposition 6 answers negatively for n ≥ 6, and Section 5 leaves n = 4, 5 open."
strata_touched:
  - D5/S3/Quantum/Matrix/ChenDeyNaiveEquationsFive
license: citation-only
triage: anchor
---

# Chen and Dey, The 4 × 4 orthostochastic variety

J. Chen and P. Dey, *The 4 × 4 orthostochastic variety*, Experimental Mathematics 32(4) (2023), 692–700; arXiv:2001.10691v1.

## Verified locator

DOI: 10.1080/10586458.2021.1982427

Source: https://arxiv.org/abs/2001.10691

The source quotations and page numbers below refer to arXiv:2001.10691v1, https://arxiv.org/pdf/2001.10691v1. The journal version of record has not been checked.

## Source statements

Section 1, page 1: "A real square matrix is called orthostochastic if it is the entrywise square of an orthogonal matrix."

After Definition 4, page 4: "a doubly stochastic matrix A satisfies C_{i,j} = 0 if and only if there exist choices of signs ε_1, …, ε_{n−1} such that with these choices of signs, the entrywise square roots of the i-th and j-th columns of A become orthogonal."

Question 5 (cf. Chterental–Đoković, Remark 3.4), page 4: "Do the naive equations define the orthostochastic variety inside B_n? In other words, if a doubly stochastic matrix satisfies C_{i,j}, R_{i,j} = 0 for all i < j, must it be orthostochastic?"

Proposition 6, page 4: "For n ≥ 6, there exists a doubly stochastic matrix which satisfies C_{i,j}, R_{i,j} = 0 for all i < j, but is not orthostochastic. Thus Question 5 has a negative answer for n ≥ 6."

Section 5, page 7: "Next, for n = 4, 5 it remains open whether the naive equations cut out the orthostochastic variety inside the Birkhoff polytope set-theoretically."

## Mathematical reading

The column and row equations are represented by the source's equivalent signed-square-root orthogonality condition. A sign on every summand is equivalent to fixing the first sign to +1, since simultaneous sign reversal preserves a zero sum. Each unordered pair is counted once, using i < j; the column and row conditions together give n(n−1) equations. Lean uses zero-based Fin n indices, real orthogonal matrices and the existing entrywise squared-norm operation RHLinalg.normSqMatrix. The claim concerns exactly n = 5.

The matrix (4J−3I)/17 supplies a negative answer at n = 5. Pairwise sign choices cancel the terms 2/17, 2/17, 4/17, 4/17, 4/17. A global orthogonal lift, multiplied by √17, would be an integer matrix with determinant squared 17⁵, which is impossible. The n = 4 question remains open. Proposition 6 already covers every n ≥ 6.

## Literature boundary

The arXiv v1 source and the screen recorded in issue #17606 locate no prior answer at n = 5. Completeness is ASSUMED-UNVERIFIED: the journal versions of record, Seberry–Lam (1982) and Lam (1983) have not been read. The constant-ratio symmetric obstruction in Turek–Cheon, arXiv:1104.0408, Theorem 6.5, is credited; the odd-order family is not formalized here.
