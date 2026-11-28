# Passive fragmented response

## Abstract

The sharp linewidth bound and minimum loss rank for each fragmented Jordan partition.

**Theorem 1.1 (Sharp response and simultaneous minimum loss rank).**

$$\begin{aligned}&\forall b,p\in \mathbb{N},\quad m:\mathrm{Fin}(b)\to \mathbb{N}_{> 0},\quad E\in \mathbb{C},\\&[2\le b\land 2\le p\land \beta> 0\land (\forall j\in \mathrm{Fin}(b),m_{j}\le p)\\&\quad \land (\exists j\in \mathrm{Fin}(b),m_{j}=p)]\longrightarrow\\&[(\forall H\in \mathcal{A}(E,m),\\&\quad N_{H}^{p-1}\neq 0\land \left\lVert N_{H}^{p-1} \right\rVert\le \beta^{p-1}\land \operatorname{rank}\Gamma(H)\ge b\\&\quad \land (\forall z\in \mathbb{C}, \neg \operatorname{IsUnit}(zI-H)\Leftrightarrow z=E)\\&\quad \land (\forall z\in \mathbb{C}, z\neq E\Rightarrow (zI-H)^{-1}=\sum_{k=0}^{p-1}\frac{N_{H}^{k}}{(z-E)^{k+1}}))\\&\land (\exists W\in \mathcal{A}(E,m), \left\lVert N_{W}^{p-1} \right\rVert=\beta^{p-1}\land \operatorname{rank}\Gamma(W)=b)].\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Eigenstructure/WiersigFragmentedResponse.sharp_passive_fragmented_response` (`✓ std3`). ∎

*Resolves.* `Problems/wiersig-2026-passive-fragmented-response` (proved) by `D5/S1/Eigenstructure/WiersigFragmentedResponse.sharp_passive_fragmented_response`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wiersig-2026-passive-fragmented-response","declaration_gid":"D5/S1/Eigenstructure/WiersigFragmentedResponse.sharp_passive_fragmented_response","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jan Wiersig (2026). *Rank-One Loss Maximizes the Spectral Response Strength of Passive Full-Order Exceptional Points*. DOI: [10.1103/5451-5wd1](https://doi.org/10.1103/5451-5wd1). URL: <https://arxiv.org/pdf/2610.31268v1>.

*Commentary.*

The closing paragraph of Wiersig's Section VIII (Conclusion) asks whether the passive response bound and rank-one optimality extend to fragmented exceptional points. The resolution here concerns a collision at a sole eigenvalue E with strictly positive linewidth, two or more blocks, and a largest block of size at least two.

The entire partition is prescribed by a positive size function m on Fin(b). Write m_j for m(j). The largest size p bounds every size and occurs among them. Positions(m) is the dependent sum of Fin(m(j)) over the block labels j. The complex matrices use orthonormal coordinates indexed by Positions(m).

Write N_H = H − EI, β = −2 Im E, and Γ(H) = i(H − H*), where * denotes conjugate transpose. The matrix norm is the Euclidean operator norm, and rank is over the complex numbers. The admissible class 𝒜(E,m) consists of complex square matrices on Positions(m) with positive semidefinite Γ(H) and a complex linear basis B of the entire coordinate space indexed by Positions(m). For every natural r, every block label j, and every position a in Fin(m(j)), the basis satisfies $N_{H}^{r} B_{j,a} = B_{j,a+r}$ when a+r < m(j), and $N_{H}^{r} B_{j,a} = 0$ otherwise.

For every passive matrix of the given partition, E is the sole eigenvalue. The resolvent is the finite Laurent sum away from E and its highest-order coefficient N^(p−1) is nonzero. The coefficient norm is at most the linewidth to power p−1 and the loss rank is at least b. One matrix of the same partition attains both bounds. In particular the minimum feasible loss rank is b, which makes rank-one loss infeasible in this fragmented setting.

The normalized Cayley transform gives the norm bound. Restricting the loss to the eigenspace gives an injective map. For attainment use the orthogonal sum S of lower unit shifts and A = (I−S)^−1 − I. Each normalized loss block is the all-ones matrix. The largest block supplies a unit vector on which A^(p−1) has norm one. Ranks of powers give the prescribed chain multiplicities, and the nilpotent Jordan-chain theorem gives a basis with those sizes.

Collisions embedded in a spectrum with spectator eigenvalues and the physical response measured by the Frobenius norm are outside this theorem's scope.

## References

- Truth anchor: `D5/S1/Eigenstructure/WiersigFragmentedResponse.sharp_passive_fragmented_response`
- Dependency: [D5/S1/Eigenstructure/NilpotentJordanChains](NilpotentJordanChains.md)
