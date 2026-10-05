---
bibkey: lee2026quantumcerny
authors: Pui Hang Lee, Pui Yee Lee and Bjørn Kjos-Hanssen
year: 2026
title: "Quantum Černý complexity of binary words"
doi: null
url: https://arxiv.org/abs/2609.40154
claim: "The quantum Černý complexity qc(w) is the least d for which two quantum channels on d x d density matrices and a start state make w the unique shortest synchronizing word; 2 <= qc(w) <= ceil(sqrt(|w|+1)), qc(0^m) = ceil(sqrt(m+1)), qc(01^n0) = 2; open problem 1 conjectures qc(01101001) = 2."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation
license: citation-only
triage: anchor
---

# Quantum Černý complexity of binary words

arXiv:2609.40154v1 (2026-09-30; primary quant-ph, cross-list cs.DM). Definition
1.1 reads:

> Let $d\ge 1$. An *instance* is a tuple $(d,A_0,A_1,\rho_0)$ where $A_0,A_1$
> are quantum channels on the $d\times d$ density matrices and $\rho_0$ is a
> $d\times d$ density matrix. For a word $u=u_1\cdots u_k\in\{0,1\}^*$ write
> $A_u=A_{u_k}\circ\cdots\circ A_{u_1}$ (letters applied left to right), with
> $A_\varepsilon=\mathrm{id}$. The *reachable set* is
> $R=\{A_u(\rho_0):u\in\{0,1\}^*\}$. A word $w$ is *synchronizing* for the
> instance if $A_w$ is constant on $R$, i.e. there is a density matrix
> $\rho_1$ with $A_w(\rho)=\rho_1$ for all $\rho\in R$. The *quantum Černý
> complexity* $\qc(w)$ of a nonempty word $w\in\{0,1\}^*$ is the least $d$ such
> that some instance of dimension $d$ has $w$ as its *unique shortest*
> synchronizing word.

The discussion section lists open problems; item 1 reads

> (Thue--Morse prefix.) We conjecture $\qc(01101001)=2$; the bound
> $\qc(01101001)\le3$ follows from Theorem~\ref{thm:kmp}. More generally,
> characterize $\{w:\qc(w)=2\}$.

and item 3 asks for $\qc(w)$ of a uniformly random word, noting that "it is
consistent with our results that $\qc(w)=2$ for almost all $w$".

## Verified locator

- URL: https://arxiv.org/abs/2609.40154 (v1, the only version; source file
  `quantum-cerny__2_.tex`, md5 `7c67e915a9bfc1f8c57ffcfcce55016c`).
- The authors' Lean formalization, https://github.com/bjoernkjoshanssen/quantumcerny,
  proves `qc(01101001) ≤ 3` and leaves the conjecture unformalized.
