---
bibkey: zhu2024thirdmoments
authors: H. Zhu, C. Mao, C. Yi
year: 2024
title: "Third moments of qudit Clifford orbits and 3-designs based on magic orbits"
doi: 10.48550/arXiv.2410.13575
url: https://arxiv.org/abs/2410.13575v1
claim: "Conjecture 2: for an odd prime d and |Ψ⟩ ∈ H_d^{⊗n}, 0 ≤ κ(Ψ,𝒯) ≤ 1 for every stochastic Lagrangian subspace 𝒯 ∈ Σ(d), together with three aggregate inequalities that follow from it; κ(Ψ,𝒯) = tr[R(𝒯)(|Ψ⟩⟨Ψ|)^{⊗3}], R(𝒯) = r(𝒯)^{⊗n}, r(𝒯) = Σ_{(x;y)∈𝒯} |x⟩⟨y|."
strata_touched:
  - D5/S3/Quantum/Magic/CliffordThirdMomentNegativity
license: citation-only
triage: anchor
---

# Zhu, Mao and Yi, third moments of qudit Clifford orbits

H. Zhu, C. Mao and C. Yi, *Third moments of qudit Clifford orbits and 3-designs based on magic
orbits*, arXiv:2410.13575v1 (17 October 2024; quant-ph, cross-listed math-ph); Commun. Math.
Phys. 407, 242 (2026), DOI 10.1007/s00220-026-05583-8.

## Verified locator

DOI: 10.48550/arXiv.2410.13575.
Primary version: https://arxiv.org/abs/2410.13575v1 (the only arXiv version).
The TeX source `3rdMoment.tex` of v1 supplies the stochastic Lagrangian subspaces
(`sec:SLSspanningSet`), the operators $r(\mathcal T)$ and $R(\mathcal T)$ (`eq:rRT`), the
definition of $\kappa(\Psi,\mathcal T)$ (`eq:kappapsiT`) and Conjecture 2 (`con:kappaTLUB`,
Eq. (147)).

## Source statements

Stochastic Lagrangian subspaces: "A subspace $\caT \leq \bbF_d^{2t}$ ... is a \emph{stochastic
Lagrangian subspace} if it satisfies the following three conditions: $\bfx \cdot \bfx - \bfy \cdot
\bfy = 0$ for any $(\bfx;\bfy) \in \caT$. $\caT$ has dimension $t$. $\mathbf{1}_{2t} \in \caT$."
$\Sigma(d):=\Sigma_{3,3}(d)$.

Operators: "$r(\caT):= \sum_{(\bfx;\bfy) \in \caT} |\bfx\> \<\bfy|, \quad R(\caT):= r(\caT)^{\otimes n}$".

Moments: "$\kappa(\Psi,\caT):=\tr[R(\caT)(|\Psi\>\<\Psi|)^{\otimes 3}]$".

Conjecture 2: "Suppose $d$ is an odd prime and $|\Psi\>\in\caH_d^{\otimes n}$. Then
$0\leq \kappa(\Psi,\caT)\leq 1 \quad \forall \caT\in \Sigma(d), \quad 6\leq \kappa(\Psi,\Sigma(d))\leq 2d+2, \quad 0\leq \kappa(\Psi,\scrT_\ns)\leq 2d-4, \quad \kappa(\Psi, \scrT_\iso)\geq 6.$"
followed by "If the first inequality in \eref{eq:kappaTLUBcon} holds, then all inequalities hold
thanks to \lref{lem:kappaTLUB}."

## Scope

The paper proves $-1\le\kappa(\Psi,\mathcal T)\le1$ in general (Lemma 20), the conjecture for
$d=3$, $\kappa=1$ for stabilizer states (Proposition 4) and nonnegativity for its cubic-phase
magic-state families.
