---
bibkey: miaofukai2026novel
authors: Yuan Miao, Kohei Fukai
year: 2026
title: "A Novel Algebraic Approach to Medium-Range Solvable Models"
doi: null
url: https://arxiv.org/pdf/2611.29351v1
claim: "Equations (40), (45)–(46), (50), (57)–(59), and (69)–(71) specify the local generators, projector charge, and Hamiltonian densities in the periodic Rydberg-blockade ladder representation. Section V ends with a qualitative expectation about fragmentation in four models."
strata_touched:
  - D5/S3/Quantum/SpinChains/MiaoFukaiGuardedMoves
  - D5/S3/Quantum/SpinChains/MiaoFukaiHamiltonians
license: citation-only
triage: anchor
---

# The periodic ladder representation

## Verified locator

- PDF v1, pp. 6–9 and 11 (paper pagination), https://arxiv.org/pdf/2611.29351v1
- Section V, final remark, https://arxiv.org/html/2611.29351v1#S5.p13.1

## Operators and normalization

Equations (69)–(70) give the empty rung and the symmetric and antisymmetric one-boson rungs. The nearest-neighbour blockade is cyclic. The generator $S_j$ is the projected exchange of the empty and symmetric rung at $j$, plus the simultaneous exchange of the two signs at $j-1$ and $j+1$ when both are occupied. The projector is $P_j=n_j^-+(n_{j-1}^{(e)}-n_{j+1}^{(e)})^2$. The control in Eq. (40) is $C_j=(P_{j-1}-P_{j+1})^2$ and $T_j=C_jS_j$. The unextended charge is $N_P=\sum_jP_j$ in Eq. (45).

Equation (46) prints $T_j-\Delta T_j^2$ and $C_j(S_j+\Delta S_j^2)$ as equal. On the periodic ladder for $L\ge5$, $T_j^2=C_jS_j^2$, so the two expressions agree after reversing the coupling. The two plus-sign diagonal pieces of the explicit ladder density in Eq. (71) give the plus-sign expression. Equation (50) fixes the minus-sign base at $\Delta=\cos\mu$ after the scalar shift. At $L=12$, with one minus at zero-based rung 0 and all other rungs empty, $T_2^2$ has diagonal entry 1. The two Eq. (46) expressions then differ on that entry whenever $\Delta\ne0$.

For even $L$, the normalized right side of Eq. (57) adds Eq. (58) at the ordered one-based pairs $(2,3),\ldots,(L,1)$. Writing $X=T_j$ and $Y=T_{j+1}$, it uses the ordered monomials $YX, XY, X^2Y^2, YX^2, Y^2X, XY^2, X^2Y$. The coefficients in the same order are $\alpha_+,\alpha_-,2\alpha_+\alpha_-\cos\mu,\kappa_+,\kappa_+,\kappa_-,\kappa_-$, where Eq. (59) gives $\alpha_\pm=\sin v_0/\sin(v_0\pm\mu)$ and $\kappa_\pm=\pm\sin\mu/\sin(v_0\pm\mu)-1$. This expression is used where both denominators are nonzero. Its analytic identification with the derivative of Eq. (51) remains open in the formalization. The regular domain for that derivative also requires $\sin\mu\ne0$.

## Fragmentation scope

The paragraph after Eq. (71) states an expectation for the four representations in Table I. The quantified tile construction in the formalization gives a lower bound within one native charge sector of the periodic ladder. Its count concerns the exhibited singleton components. The full component count, the largest-component asymptotics, and the corresponding results for the other representations remain open here. The folded-chain jamming criterion and fixed-number enumeration in [Zadnik and Fagotti, §4.3, Eqs. (53)–(59)](https://arxiv.org/abs/2009.04995) concern a different basis and carrier. The ladder mappings in [Eck and Fendley, §§4.2–4.3](https://arxiv.org/abs/2302.14081v4) use distinct source boundary conditions for the two symmetry sectors.
