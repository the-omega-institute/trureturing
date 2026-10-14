---
bibkey: rajchelkorzekwapuchalazyczkowski2021birkhoff
authors: Grzegorz Rajchel-Mieldzioć, Kamil Korzekwa, Zbigniew Puchała, Karol Życzkowski
year: 2021
title: "Algebraic and geometric structures inside the Birkhoff polytope"
doi: 10.1063/5.0046581
url: https://arxiv.org/abs/2101.11288
claim: "Section V asks whether the bracelet condition suffices for unistochasticity of circulant matrices for d > 4; Definition 7 gives the bracelet inequalities and Theorem 17 settles d = 4."
strata_touched:
  - D5/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic
license: citation-only
triage: anchor
---

# Circulant matrices and bracelet conditions in the Birkhoff polytope

## Verified locator

DOI: 10.1063/5.0046581 (J. Math. Phys. 63, 012202 (2022)).

Source: https://arxiv.org/abs/2101.11288. The arXiv v1 PDF supplies Definition 4 on page 3, Definitions 5 and 7 on page 4, Theorem 17 on page 9, and Section V on page 13.

## Source statements

Definition 4, page 3: “The set of d × d unistochastic matrices U_d consists of all bistochastic matrices B whose entries satisfy B_jk = |U_jk|² for some unitary matrix U.”

Definition 5, page 4: “The set of d × d circulant matrices C_d consists of all matrices B whose entries satisfy [30] B_{j+l,k} = B_{j,k−l}, (7) where the addition and subtraction is modulo d.”

Definition 7, page 4: “The set of d × d bracelet matrices L_d consists of these bistochastic matrices B whose entries satisfy:” followed by (9a) 2 max_j √(B_jk B_jl) ≤ Σ_j √(B_jk B_jl) and (9b) 2 max_l √(B_jl B_kl) ≤ Σ_l √(B_jl B_kl), “which are called column and row bracelet conditions.” The paragraph below counts d(d−1) conditions, one for each unordered pair of distinct columns and of distinct rows.

Theorem 17, page 9: “The set of circulant unistochastic matrices, C₄ ∩ U₄, coincides with the set of circulant bracelet matrices C₄ ∩ L₄.”

Section V, page 13: “Another observation that holds for d ≤ 4, and should be further investigated for d > 4, is whether the bracelet condition is sufficient for unistochasticity if we restrict the analysis to the set of circulant matrices.”

## Mathematical scope

Matrices use zero-based indices in Fin d. Matrix.circulant has entries v(i−j), giving the same class as Definition 5. Unistochasticity uses RHLinalg.normSqMatrix of a complex unitary matrix. The bracelet predicate includes bistochasticity and both inequalities for distinct pairs; finite indexed suprema represent the displayed maxima.

The repository refutation uses d = 12 and entries 1/6 at offsets j−i in {0,1,3,4,6,9}, with all other entries zero. It leaves the source's d ≤ 4 statements intact and does not decide Conjecture 9 or Conjecture 19.
