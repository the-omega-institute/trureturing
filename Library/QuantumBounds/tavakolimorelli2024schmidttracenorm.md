---
bibkey: tavakolimorelli2024schmidttracenorm
authors: Armin Tavakoli; Simon Morelli
year: 2024
title: "Enhanced Schmidt number criteria based on correlation trace norms"
doi: 10.1103/PhysRevA.110.062417
url: https://arxiv.org/abs/2402.09972v2
claim: "For a bipartite state of Schmidt number at most r, the trace norm of the table of joint probabilities of local SIC measurements or of complete sets of MUBs is bounded (Results 1 and 2), and for incomplete measurements (n > d equiangular effects, or m < d + 1 MUBs) the bounds of Eqs. (51) and (53) hold. Conjecture 2 asserts ‖P_n‖_tr ≤ [d(d − 1) + r(n − d)]/[n(n − 1)] for equiangular measurements (Eq. (52)), and Conjecture 3 asserts ‖Q_m‖_tr ≤ 1 + (m − 1)r/d for m MUBs (Eq. (54)); the introduction leaves deciding these conjectures as an open problem."
strata_touched:
  - D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM
  - D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB
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

## Reading used by the repository

Both sides measure with the same d and the same n (EAMs, n > d) or m (MUBs, 1 ≤ m ≤ d), with independently chosen families. The entries of P_n and Q_m are the joint probabilities tr[ρ (E_a ⊗ F_b)] of the local effects; for MUBs the effects are the md rank-one projectors. A state has Schmidt number at most r if it is a finite convex combination of unit vectors whose coefficient matrices have rank at most r. Since both bounds increase with r, "Schmidt number r" is read as "Schmidt number at most r".
