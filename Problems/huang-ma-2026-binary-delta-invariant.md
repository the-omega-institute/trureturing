---
slug: huang-ma-2026-binary-delta-invariant
bibkey: huangma2026mutation
doi: 10.1016/j.jalgebra.2026.07.040
url: https://arxiv.org/abs/2602.03194v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/ClusterMutation/HuangMaBinaryDeltaInvariant.result
---

# Huang–Ma Remark 2.7: the binary delta invariant

## Problem

Min Huang and Qiling Ma, *A mutation invariant for skew-symmetrizable matrices*, arXiv:2602.03194v1, Remark 2.7; Journal of Algebra 712 (2027), 546–558. The [source note](../Library/Eigenstructure/huangma2026mutation.md) gives the verified locator and verbatim definitions.

> We also conjecture that for any fixed n and any choice of skew-symmetrizer d₁, …, dₙ, the invariant δ is binary. This is supported by several explicit computations.

For an integer matrix $B$, fix positive integer weights $d_i$ with $d_i b_{ij}=-d_j b_{ji}$. The real symmetric matrix $S(B)$ has diagonal $2$, upper entries $\operatorname{sgn}(b_{ij})\sqrt{|b_{ij}b_{ji}|}$ and lower entries $\operatorname{sgn}(b_{ji})\sqrt{|b_{ij}b_{ji}|}$. The invariant is $\delta(B)=\det S(B)\pmod4$. Binary means at most two residues for fixed size and weights, without asserting that both are attained.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Fixed matrix size and fixed positive integer skew-symmetrizer | `claim` quantifies the natural size and positive vector before choosing the two residues | Same quantifier order; the empty matrix is included as an extension |
| The diagonal skew-symmetrizer makes the matrix skew-symmetric | `IsSkewSymmetrizer` is positivity and the literal entrywise skew relation | Diagonal zero follows from the relation and positivity |
| The three cases defining the real symmetrization | `symmetrization` uses diagonal 2, integer sign, absolute value and real square root | Same ordered-index expression |
| The determinant is an integer and its residue is binary | `claim` chooses an integer determinant and one of two residues for every admissible matrix; `result` proves it | Integrality is included explicitly; the two residues may coincide |

## Motivation

[Preregistration #18784](https://github.com/the-omega-institute/trureturing/issues/18784) identifies the published named conjecture, its literal conventions and the literature screen. The settlement uses `admission_basis: open-problem-resolution (#18784; Proved)`. It makes no priority claim beyond the searched literature.

## Gap

The real radical matrix does not directly expose the arithmetic restriction modulo four. A fixed positive diagonal symmetrizer supplies both an integral companion and a common square-class constraint. The explicit valuation formula for the even-size nonzero residue is outside the formalized statement.

## Route

Write $A_{ii}=2$, $A_{ij}=b_{ij}$ for $i<j$, and $A_{ij}=-b_{ij}$ for $i>j$. The identity $D^{1/2}A=S(B)D^{1/2}$ gives $\det S(B)=\det A\in\mathbb Z$. For odd size, the weighted skew determinant vanishes and $A\equiv B\pmod2$, so $\delta(B)\in\{0,2\}$.

For size $2m$, inversion of whole permutations in the determinant expansion gives

$$\det A\equiv(-1)^m\det B\pmod4.$$

If $\det(DB)=0$, it is already a square. If $\det(DB)\ne0$, the rational alternating form associated to $DB$ is nondegenerate, so it has a symplectic basis and $\det(DB)$ is a square. The frozen `D5.S3.QuadraticForms.SymplecticBasis.exists_isSymplecticBasis` and its pairing equations supply the basis used by `alternating_det_square`. The resulting identity says that $\Delta\det B$ is an integer square, where $\Delta=\prod_i d_i\ne0$.

If $\Delta q$ and $\Delta q_0$ are squares, cancellation over the rationals makes $q q_0$ an integer square. Any two nonzero residues $a,b\in\mathbb Z/4\mathbb Z$ whose product is a square coincide. Choosing one attained nonzero residue therefore leaves at most that residue and zero. This pairwise argument avoids choosing a valuation or an explicit nonzero residue.

## Falsifier

A fixed size and positive symmetrizer admitting three determinant residues would contradict `claim`. Every delivered declaration is checked without `sorry`, and the axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}. No mathematical residual remains for the existential binary claim.

## Evidence

The settling declaration is `D5.S3.Combinatorics.ClusterMutation.HuangMaBinaryDeltaInvariant.result : claim`. Its public surface consists of `IsSkewSymmetrizer`, `symmetrization`, `claim` and `result`. The odd-size statement is the private helper `odd_binary`, used by `result`. The determinant congruence is the private helper `companion_congruence`; `weighted_det_square` and `weighted_square_residues` supply the even-size arithmetic restriction.

The escape audit for `result` is unfinished: [issue #18988](https://github.com/the-omega-institute/trureturing/issues/18988). No Reg registration is delivered. An enrolled template with exact reconstruction of the universal size/weight parameters, the existential uniform residue choice, and all subsequent matrices lacks compiled bridge and variation/sensitivity evidence. The mathematical settlement does not assert completion of that audit.

### Experiment

[Experiment directory at commit `2d7247cb9a8d67c172b5755a8fd40e027e8c4c93`](https://github.com/the-omega-institute/trureturing-experiments/tree/2d7247cb9a8d67c172b5755a8fd40e027e8c4c93/docs/reports/huang-ma-2026-remark-2-7-binary-delta).

Command: `python3 /Users/auric/trureturing-experiments/docs/reports/huang-ma-2026-remark-2-7-binary-delta/check.py`; exit 0, `RESULT PASS`. The pinned `check.py` has SHA-256 `15b654701057c742fe05c7b76fe489d9e5b888466e8a8fd54fede32b7949cd50`. The same program can be run as `python3 check.py` from the linked directory.

The floating companion-determinant comparison covers 400 random matrices of sizes 2–6, with maximum relative difference $5.3\times10^{-14}$ (rounded). The even-size determinant congruence has zero failures in 900 random matrices of sizes 2, 4 and 6. Exhaustive enumeration covers 26 symmetrizers at sizes 1–4 with each pair parameter in $[-2,2]$, up to 15625 matrices per symmetrizer. Random enumeration covers 3000 matrices for each of 12 symmetrizers at sizes 5 and 6. Every computed residue set has at most two elements and lies in the program's predicted set. These finite computations support no additional universal claim.

## Triage

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| Huang–Ma Remark 2.7 | **Proved — kernel-checked:** `result` proves the exact existential binary claim, including integrality, for every natural size and positive symmetrizer. |
| Whole-permutation inversion | **Proved — kernel-checked supporting identity:** `companion_congruence` pairs determinant terms using permutation inversion and is consumed by `result`. |
| Pairwise square-class cancellation | **Proved — kernel-checked supporting identities:** `square_weight_cancel` and `weighted_square_residues` restrict all nonzero attainable residues to one value. |
| Odd-size residue set | **Proved — kernel-checked:** `odd_binary`, consumed by `result`, gives the set $\{0,2\}$. |
| Explicit even-size valuation formula | **Open as a Lean extension:** the formula using the 2-adic valuation and odd part of $\prod_i d_i$ is not formalized; `result` proves existence of two residues without identifying the nonzero residue. |
| Complete mathematical settlement | **Proved — kernel-checked:** `result` leaves no mathematical residual for `claim`. |
| Escape registration | **Open audit evidence:** the four-slot escape audit is unfinished in #18988; no Reg registration is delivered. |
| The skew-symmetric case $d_i=1$ | **Proved in prose:** $\Delta=1$ makes $\det B$ an integer square. Squares modulo four are 0 or 1; the signed companion congruence gives $\{0,1\}$ when the size is divisible by four and $\{0,3\}$ when it is 2 modulo four. The odd case is $\{0,2\}$. This specializes the general proof and adds no separate Lean declaration. |
| Sharpness of the binary bound | **Computed:** in the stated exhaustive scope, weights $(1,2,4)$ and $(1,2,4,8)$ attain only residue 0. This finite reading does not prove that all matrices for those weights have residue 0. |
| Universal attainment classification | **Open here:** which positive symmetrizers attain both permissible residues is not settled. |
| Source's extension for pairwise coprime symmetrizers | **Open here:** neither a Lean theorem nor an experiment in this delivery settles the distinct extension. |
| Consequences for the source | **Proved — kernel-checked:** the fixed-symmetrizer binary assertion needs no coprimality assumption. No claim about mutation invariance or the source's other extensions is added. |
| Literature status | **Literature reading:** arXiv v1 Sections 1–2 and Crossref/OpenAlex metadata are the source screen recorded in #18784; no settlement was found within that search. Completeness is **ASSUMED-UNVERIFIED**. |

The decisive mechanism is the integral companion congruence together with one common nonzero square class. Positivity supplies the invertible real diagonal change of basis and a nonzero weight product; no coprimality of the weights is needed. The proof includes size zero, whose determinant is one, and makes no claim that both permissible residues occur.

## ASSUMED-UNVERIFIED

Literature completeness and worldwide priority are not established. The journal full text was not read; whether it changes Remark 2.7 relative to arXiv v1 is ASSUMED-UNVERIFIED. The explicit even-size residue formula and the attainment classification are not formalized. The finite experiment does not establish those universal extensions. Four-slot escape registration remains unfinished under #18988.
