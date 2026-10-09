---
slug: gupta-iosevich-2026-edge-complexity-weak-product
bibkey: gupta2026edgecomplexity
doi: 10.48550/arXiv.2607.15598
url: https://arxiv.org/abs/2607.15598v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation.result
---

# Weak-product closure of the edge-complexity equality class

## Problem

V. Gupta, A. Iosevich, J. Iosevich, B. Song and H. Tian, *Edge complexity of graphs*, arXiv:2607.15598v1, Section 3, Remark after Corollary 3.10:

> Remark. The coprimality hypothesis is not merely a technicality in the present argument: it is what permits the product labeling to be viewed as a cyclic labeling. Proposition 3.7 does not prove closure under arbitrary weak products. Consequently, unrestricted closure of the equality class under the weak product has not been established. Whether such closure holds is a natural open question.

The assertion is that any two finite simple graphs with positive size satisfying $\operatorname{FR}_{\min}(G)=E(G)/\sqrt{2s(G)}$ have a weak product satisfying the same equality. Definition 3.1 gives adjacency precisely when both coordinate pairs are adjacent. The Fourier transform has coefficient $1/N$, the numerator of $\operatorname{FR}$ is entrywise $\ell^1$, and the denominator is Frobenius; $E$ is the sum of the absolute adjacency eigenvalues.

## Motivation

The settling declaration `D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation.result` disproves this universal closure assertion with $G=H=K_3$. It reuses the frozen direct product `DirectProductCyclePathBootstrap.dirProd`, Fourier matrix `PolygonalFourierCouplings.fourier`, its unitarity through `TomiyamaDiagonalKPositivity.fourierRows_gram`, the Frobenius facts `CartesianVariance.frobSq_eq_sum`, `CartesianVariance.frobSq_star` and `CommutatorGap.frobSq_unitary_right`, and the stochastic and spectral-trace facts from `RHLinalg` in `VonNeumann` and `PosIndex`.

## Gap

Preregistration [#14729](https://github.com/the-omega-institute/trureturing/issues/14729) identifies the quoted question, the full quantifiers, the counterexample and the source checks. Its literature readings cover arXiv versions and related author papers, MathDB, formal-conjectures (seat-reported) and the repository. No resolution was found in those recorded scopes. George–Sanders concerns circulancy rather than energy equality; its theorem supplies the family argument below, not a dependency of this Lean module.

## Route

Both factors $K_3$ have size $3$, energy $4$ and $\operatorname{FR}_{\min}=4/\sqrt6$, so they attain equality. Write $A$ for the adjacency matrix of $K_3\times K_3$. Its size is $18$, energy $16$, and

$$A^2=2J+2I-A,\qquad S_g=(6A+3I-2J)/9,\qquad S_g^2=I,\qquad \operatorname{tr}(S_gA)=16.$$

For any labeling put $M=FAF$ and $W=FS_gF$. Unitarity and the trace pairing give $16\leq\|M\|_1$; Parseval gives $\|M\|_2=6$. Equality would force at most one nonzero per column of $M$, hence $MM^*$ diagonal and $A^2$ circulant. The strongly regular identity then makes $A$ circulant. The kernel checks all $2^9$ binary first rows and excludes every circulant satisfying that identity. Consequently $\operatorname{FR}_{\min}(K_3\times K_3)>8/3$.

## Falsifier

A labeling of $K_3\times K_3$ attaining $8/3$, a discrepancy between the source and the public definitions, or a nonstandard axiom in `result` would invalidate this settlement. The compiled refutation covers all labelings, not only the numerical enumeration. The finite vertex witness is inhabited by $(0,0)$.

## Evidence

`result : ¬ claim` is the kernel-checked public settlement. The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9). Its private helpers are consumed on the proof path. The admission basis is `open-problem-resolution` (#14729; Refuted), independently of the bind-only judgement form. The Scribe resolution node records Proved for the statement `¬ claim`; the source closure assertion is Refuted.

## Triage

### What the settlement shows

- **Proved (literature and kernel-checked specialization): equality mechanism.** Source Theorem 2.1 proves at most one nonzero Fourier entry in each row and column, and Theorem 2.8 proves the circulancy of $A^2$. In this module `equality_entry_norm`, `equality_column_unique` and `equality_gram_diagonal` prove the column and Gram consequences needed by the sign-matrix bound, and `square_circulant_of_sparse` proves the resulting circulancy of $A^2$. The full general row-and-column criterion is a literature statement, not an additional public Lean theorem.
- **Proved (kernel-checked private helpers): strongly regular obstruction.** `p3_srg` and `p3_labeled_srg` prove $A^2=2J+2I-A$ for the $\operatorname{srg}(9,4,1,2)$ witness and every labeling. `product_l1_ne` derives circulancy of $A$ from that of $A^2$. `no_bool_circulant` and `no_real_circulant` exclude every binary circulant first row on $\mathbb Z_9$ satisfying $C^2=2J+2I-C$.
- **Proved (kernel-checked private helpers and result): explicit sign-matrix bound.** `rawSign_square`, `rawSign_unitary`, `rawSign_trace`, `product_pairing` and `product_l1_bound` establish the displayed sign-matrix identities and bound without diagonalizing $A$. `product_fr_strict`, `product_frmin_strict`, `product_not_attains` and `result` give the strict bound and refutation. `p3_energy` separately computes the energy through the polynomial identity and Hermitian trace facts.
- **Computed (NumPy floating point): numerical minimum.** The pinned experiment entry below runs with `python3 check.py` and exits 0; SHA-256 `6bbb87a00f12b5d104d1d22efda37a7811035f385af407374eecce186648d294`. It reports $E=16$, $s=18$, lower bound $8/3$, and minimum $3.6076494185398573$ over all $8!=40320$ labelings fixing label zero. It also checks the strongly regular and sign-matrix identities and reports zero circulant solutions among $2^9$ first rows. This is numerical evidence, not a kernel-certified exact minimum. Every labeling differs from one fixing zero by a cyclic shift: shift the label of any fixed vertex to zero. The Fourier entries then acquire factors $e^{2\pi i(m+n)c/N}$ of modulus one, so the ratio is unchanged; the tested representatives cover all labelings.
- **Open: exact closed form.** A closed form for the exact minimum is not established by the numerical computation.
- **Proved (complete paper argument with literature inputs): the family.** For $a,b\geq3$ and $\gcd(a,b)>1$, $K_a\times K_b$ fails equality. Each complete graph is a cyclic Cayley graph and attains equality by source Theorem 1.1. The product adjacency is $(J_a-I_a)\otimes(J_b-I_b)$, with eigenvalues $(a-1)(b-1)$, $-(a-1)$, $-(b-1)$ and $1$. Their distinct squared values determine their signed eigenvalues: all negative values have magnitude at least $2$, the value $1$ is positive, and $(a-1)(b-1)$ is strictly larger than either negative magnitude. If $a=b$, the coincident negative values have the same sign. Let $\Lambda$ be the set of distinct eigenvalues and define

  $$p(t)=\sum_{\lambda\in\Lambda}\lambda\prod_{\mu\in\Lambda\setminus\{\lambda\}}\frac{t-\mu^2}{\lambda^2-\mu^2}.$$

  The denominators are nonzero, $p(\lambda^2)=\lambda$, and the real symmetric spectral decomposition yields $A=p(A^2)$. If the product attained equality, source Theorem 2.8 would make $A^2$ circulant in an attaining labeling. Circulant matrices form an algebra containing $I$, so $A$ would be circulant. George–Sanders, *When is a Tensor Product of Circulant Graphs Circulant?*, [arXiv:math/9907119](https://arxiv.org/abs/math/9907119), Theorem 2, excludes circulancy when $\gcd(a,b)>1$ and one order differs from $2$. This contradiction proves the family assertion. The argument is a paper result; the Lean delivery covers only $K_3\times K_3$.
- **Open: closure with a $K_2$ factor.** Closure for equality-attaining factors of noncoprime orders when one factor is $K_2$ remains unproved here.
- **Open: cyclic Cayley product classification.** The exact equality class of weak products of cyclic Cayley graphs remains unproved here.
- **Proved (paper special case):** $K_2\times K_2$ is two disjoint edges, is circulant on $\mathbb Z_4$ with connection set $\{2\}$, and attains equality by source Theorem 1.1. This single case does not prove general $K_2$-factor closure.
- **Proved (source scope): unaffected results.** Proposition 3.7 and Corollary 3.10 retain their coprime-order hypotheses. The witness has orders $3$ and $3$, so it does not refute them. Theorem 1.1's lower bound and Theorems 2.1 and 2.8's equality implications also remain compatible with the strict counterexample. Any use of unrestricted closure needs an independent restriction or proof; no such extension is claimed.

### Reproducible computation

Experiment entry: [`docs/reports/gupta-iosevich-2026-edge-complexity-weak-product/check.py`](https://github.com/the-omega-institute/trureturing-experiments/tree/602ec65402d492351ebc19230b04caa93001cda8/docs/reports/gupta-iosevich-2026-edge-complexity-weak-product) in `the-omega-institute/trureturing-experiments` at `602ec65402d492351ebc19230b04caa93001cda8`. Command: `python3 check.py` (NumPy). Exit code: 0. SHA-256: `6bbb87a00f12b5d104d1d22efda37a7811035f385af407374eecce186648d294`.

The script checks the $K_3$ equality reading, the strongly regular identity $A^2=2J+2I-A$ for $K_3\times K_3$, the sign-matrix identities $S_g^2=I$ and $\operatorname{tr}(S_gA)=16$, the minimum of $\operatorname{FR}$ over all $8!$ labelings that fix label zero (cyclic shifts make this exhaustive), and the absence of binary circulant solutions of $C^2=2J+2I-C$ on $\mathbb Z_9$.

## ASSUMED-UNVERIFIED

The floating-point minimum is not an exact algebraic value. The family assertion uses the cited paper theorems and the complete argument above; its generality is not Lean-verified by this module. Negative literature searches establish only their recorded scopes. The open $K_2$ factor and cyclic Cayley classification questions receive no settlement here.
