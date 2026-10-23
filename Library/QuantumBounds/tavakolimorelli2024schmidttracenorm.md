---
bibkey: tavakolimorelli2024schmidttracenorm
authors: Armin Tavakoli; Simon Morelli
year: 2024
title: "Enhanced Schmidt number criteria based on correlation trace norms"
doi: 10.1103/PhysRevA.110.062417
url: https://arxiv.org/abs/2402.09972v2
claim: "For a bipartite state of Schmidt number at most r, the trace norm of the table of joint probabilities of local SIC measurements or of complete sets of MUBs is bounded (Results 1 and 2), and for incomplete measurements (n > d equiangular effects, or m < d + 1 MUBs) the bounds of Eqs. (51) and (53) hold. Conjecture 2 asserts ‖P_n‖_tr ≤ [d(d − 1) + r(n − d)]/[n(n − 1)] for equiangular measurements (Eq. (52)), and Conjecture 3 asserts ‖Q_m‖_tr ≤ 1 + (m − 1)r/d for m MUBs (Eq. (54)); the introduction leaves deciding these conjectures as an open problem. Conjecture 1 asserts that, when both a SIC and a complete set of MUBs exist in the local dimensions, the two correlation trace norms satisfy ‖Q‖_tr = K‖P‖_tr with K = √(d_A(d_A+1)) √(d_B(d_B+1))."
strata_touched:
  - D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM
  - D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB
  - D5/S3/QuantumBounds/SicMubCorrelationTraceNormEquality
license: citation-only
triage: anchor
---

# Tavakoli and Morelli, Schmidt-number criteria from correlation trace norms

A. Tavakoli and S. Morelli, *Enhanced Schmidt number criteria based on correlation trace norms*, arXiv:2402.09972 [quant-ph] (v2 of 17 December 2024; v1 of 15 February 2024), Phys. Rev. A 110, 062417 (2024).

## Verified locator

DOI: https://doi.org/10.1103/PhysRevA.110.062417

Source: https://arxiv.org/abs/2402.09972v2

The text was read from the PDF https://arxiv.org/pdf/2402.09972v2:
- p. 1, the introduction;
- p. 2, §II A (Schmidt number, Eq. (2)) and §III A, Eq. (8);
- pp. 6–7, §V A–B, Eqs. (49)–(54).

## Source statements

Introduction (p. 1): "Finally, we show evidence in support of our criteria admitting resource-efficient generalisations, in which fewer measurements are used to detect the Schmidt number. Deciding these conjectures is left as an open problem."

§II A (p. 2): "the Schmidt number of ρAB is the smallest positive integer r for which it is possible to generate the state by stochastically preparing bipartite pure states that are, up to local unitary transformations, confined to an at most r-dimensional local Hilbert space. The latter is equivalent to the Schmidt rank of the pure state, written SR(ψ), being no more than r."

§III A (p. 2): "The resulting outcome statistics is given by Born's rule, P^SIC_ab = tr[ρAB E^A_a ⊗ E^B_b]. (8)"

§V A (pp. 6–7): "Consider a set of n > d pure states {|ψa⟩} in d-dimensional Hilbert space. We call the set an equiangular measurement (EAM) if the following two conditions are satisfied. Firstly, by defining the sub-normalised projector Ea = d/n |ψa⟩⟨ψa|, we can interpret {Ea}a as a quantum measurement. This is equivalent to requiring that the quantum states resolve the identity. Σ_a |ψa⟩⟨ψa| = (n/d) 1_d. (49) Secondly, the quantum states are equiangular, i.e. the modulus overlap of all distinct states (a ≠ a′) is constant; |⟨ψa|ψa′⟩|² = (n − d)/(d(n − 1)). (50)" … "Conjecture 2. For any state of Schmidt number r it holds that ‖Pn‖tr ≤ [d(d − 1) + r(n − d)]/[n(n − 1)]. (52)"

§V B (p. 7): "If only a subset of m < d+1 MUBs is used, we can define the md × md matrix ‖Qm‖tr encoding the outcome statistics when measuring with md local MUB projectors" … "Conjecture 3. For any state of Schmidt number r it holds that ‖Qm‖tr ≤ 1 + (m − 1)r/d. (54)"

## Conjecture 1 (v2 TeX source)

Quotations from the v2 TeX source `manuscript_EW_2.tex` (md5 `1eca2077b5ff264df6ff3cafb608f9a6`).

The SIC and MUB definitions (l. 158–171):

> In a $d$-dimensional Hilbert space, a SIC-POVM (or SIC measurement)  is defined as a set of positive operators $\{E_i\}_{i=1}^{d^2}$ such that $E_i=\frac{1}{d}\ketbra{\psi_i}{\psi_i}$ and
> \begin{equation}
> \left|\braket{\psi_j}{\psi_k}\right|^2=\frac{1}{d+1} \quad \forall j\neq k.
> \end{equation}

> A pair of bases of $d$-dimensional Hilbert space are called unbiased if the modulus overlap between any pair of their respective elements is identical. By extension, a set of $m$ bases is called mutually unbiased if every pair of bases are unbiased with respect to each other. Thus, if for each $z=1,\ldots, m$ we have a basis $\{\ket{g_a^z}\}_{a=1}^d$, they are mutually unbiased if and only if
> \begin{equation}\label{MUB}
> \left|\braket{g_a^z}{g_{a'}^{z'}}\right|^2=\begin{cases}
> \delta_{a,a'} & \text{if } z=z'\\
> \frac{1}{d} & \text{if } z\neq z'
> \end{cases}.

The correlation matrices and the constant (l. 190–200, 255–257):

> P^\text{SIC}_{ab}=\tr\left(\rho_{AB} E^A_a \otimes E^B_b\right).
> \end{equation}
> We write $\mathbf{P}$ for the $d_A^2\times d_B^2$ matrix whose entries are $P^\text{SIC}_{ab}$.  We will now consider the trace norm of $\mathbf{P}$. Our first result shows that this norm acts as a Schmidt number criterion.

> 	where we define a constant depending on the local dimensions $K=\sqrt{d_A(d_A+1)}\sqrt{d_B(d_B+1)}.$

> Q^\text{MUB}_{al,bk}=\bracket{g_a^l,h_b^k}{\rho_{AB}}{g_a^l,h_b^k}.
> \end{equation}
> We associate this $d_A(d_A+1)\times d_B(d_B+1)$ table of probabilities to the matrix $\mathbf{Q}=\sum_{a,l,b,k}Q^\text{MUB}_{al,bk} \ketbra{a,l}{b,k}$. Our second main results is a Schmidt number criterion based on the trace norm of this data table.

The conjecture (l. 420–423):

> \begin{conjecture}\label{equivalence}
> Provided that both a SIC and a complete set of MUBs exist in dimension $d_A$ and $d_B$, the criteria in Result~\ref{SICresult} and~\ref{MUBresult} are equivalent. It then holds that $\left\|\mathbf{Q}\right\|_\text{tr}=K\left\|\mathbf{P}\right \|_\text{tr}$.
> \end{conjecture}
> Explicit calculations show that this is indeed the case for prime dimensions smaller than 20.

## Reading used by the repository

Both sides measure with the same d and the same n (EAMs, n > d) or m (MUBs, 1 ≤ m ≤ d), with independently chosen families. The entries of P_n and Q_m are the joint probabilities tr[ρ (E_a ⊗ F_b)] of the local effects; for MUBs the effects are the md rank-one projectors. A state has Schmidt number at most r if it is a finite convex combination of unit vectors whose coefficient matrices have rank at most r. Since both bounds increase with r, "Schmidt number r" is read as "Schmidt number at most r".

For Conjecture 1 the two local dimensions may differ. P and Q are the rectangular tables of joint probabilities of the local SIC effects E_i = |ψ_i⟩⟨ψ_i|/d and of the local rank-one MUB projectors. The conjecture is read for every state and every choice of local SICs and complete MUB families.
