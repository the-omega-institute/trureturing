---
slug: cui-mehta-mousavi-nezhadi-2020-chsh-group-decomposition
bibkey: cuimehtamousavinezhadi2020chsh
doi: 10.22331/q-2020-10-21-346
url: https://arxiv.org/abs/1911.01593
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.result
---

# A product decomposition of the generalized CHSH groups

## Problem

Cui, Mehta, Mousavi and Nezhadi, *A generalization of CHSH and the algebraic structure of optimal strategies*, Quantum 4, 346 (2020), arXiv:1911.01593v5, Section 1.4 (Further work), item 2, ask:

> In Section 5, we give efficient explicit presentations for G_n and its multiplication table. Can we go further and characterize these groups in terms of direct and semidirect products of small well-known groups? The first few cases are as follows

For every natural $n\ge2$, the answer is

$$G_n\cong\left(C_{2n}\times C_2^{\,n-2}\right)\rtimes_{\alpha_n}C_n.$$

The group $G_n$ has the source's Section 5 presentation on $P_0,P_1,J$: the relators are $P_0^n,P_1^n,J^n,[J,P_0],[J,P_1]$ and $J^i(P_0^iP_1^{-i})^2$ for $1\le i\le\lfloor n/2\rfloor$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| The Section 5 presentation | `P0`, `P1`, `J`, `rels`, `G` | The relators are words equal to the identity; the negative exponent uses the integer cast of the natural index. |
| Every $n\ge2$ | `claim` quantifies over natural `n` with `2 ≤ n` | No further assumption on $n$. |
| Small cyclic factors | `L` is `Multiplicative (ZMod (2*n))` times the functions from `Fin (n-2)` to `Multiplicative (ZMod 2)` | The independent involutions have zero-based indices. |
| An explicit semidirect product | `alpha` and the `MulEquiv` in `claim` | The action is the binding action in [the definition comment on #16204](https://github.com/the-omega-institute/trureturing/issues/16204#issuecomment-6146781824). |
| A product characterization | `result : claim` | An actual multiplicative equivalence, rather than an order comparison. |

The binding comment fixes `cyclicHom`, `s`, `t`, `liftL`, `ts`, `u`, `e`, `step`, `stepAut` and `alpha`. Here `t n i` represents the source's $t_{i+1}$, and `u n k` uses one-based indices. In particular, $u_{n-1}=s^n\prod_{i=1}^{n-2}t_i$, while $u_k=1$ outside the indicated range. For $n=2$, $u_1=s^2$. The action below two is trivial; the claim has no conclusion for those values.

## Motivation

The settling declaration is `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.result`. It supplies a uniform structural answer to the source's further-work question. The source's Theorem 5.7 identifies the presented group with its observable matrix group; the new equivalence characterizes the presented group using cyclic and elementary abelian factors.

The literature locator and quoted presentation are in [the Library note](../Library/FiniteGroups/cuimehtamousavinezhadi2020chsh.md). The external question is preregistered in [#16204](https://github.com/the-omega-institute/trureturing/issues/16204); there is no digestion atom.

## Gap

The source gives four small cases and the order formula, without the displayed all-$n$ product decomposition. The kernel-checked equivalence closes this structural question for $n\ge2$. Simplification for odd $n$ and explicit correspondences to the source's even small-case decompositions remain open here.

## Route

Write $L_n=C_{2n}\times C_2^{n-2}$, with generator $s$ of the first factor and independent involutions $t_1,\ldots,t_{n-2}$. Set $t_{n-1}=s^n\prod t_i$, $e_k=st_k$ and $e_0=e_n=s$. The cyclic generator acts by $s\mapsto e_1$ and $t_i\mapsto e_{i+1}e_1^{-1}$. The orbit calculation shows that this automorphism has period dividing $n$.

The forward map sends $P_0$ to the outer cyclic generator, $P_1$ to $s$ times that generator, and $J$ to $s^2$. In the presented group, the elements $\delta_i=P_0^iP_1^{-i}$ commute. Their subgroup supports the inverse map from $L_n$. Compatibility with conjugation by $P_0$ extends it to the semidirect product. The two composites fix the generators, yielding the multiplicative equivalence.

## Falsifier

A mismatch of the source relators or the binding action would invalidate the interpretation of the settlement. The exact Lean conclusion is the preregistered `claim`, and the action data are fixed by the linked definition comment. A numerical order match alone does not prove this conclusion.

## Evidence

**Kernel-checked.** `D5.S3.Quantum.Algebra.GeneralizedCHSHGroupDecomposition.result` proves `claim`. Its axiom closure is contained in `{propext, Classical.choice, Quot.sound}`. The private helper identities named below belong to the same compiled module; they are supporting proof steps, not additional public settlements.

**Computed.** The experiment is [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/0126fd98a88134b5bac8b6a41fc47ed30247f832/docs/reports/cui-mehta-mousavi-nezhadi-2020-chsh-group-decomposition). Run `python3 check.py` in that directory. Exit code: 0; result: `ALL_OK`. The SHA-256 of `check.py` is `be0fdfe9abe9f800c0805d4b40c48fd5c8dd96abd75ec3f12b8642d9d3b384b1`. The exact tested scope is $n=2,\ldots,9$. The matrix-group orders are respectively $8,36,128,400,1152,3136,8192,20736$. Within that scope the program verifies the factor-coordinate bijection, the dependent-involution identity, the conjugation formulas and the trivial intersection with the shift subgroup. It does not compute the odd-$n$ simplified decomposition or explicit isomorphisms to the authors' $G_4,G_6$ forms.

**Escape audit unfinished.** The public audit targets are `D5.S3.Quantum.Algebra.GeneralizedCHSHGroupDecomposition.result` and the compiler-generated congruence theorems `D5.S3.Quantum.Algebra.GeneralizedCHSHGroupDecomposition.cyclicHom.congr_simp` and `D5.S3.Quantum.Algebra.GeneralizedCHSHGroupDecomposition.stepAut.congr_simp`. The latter two are compiler consequences of the definitions, not additional authored mathematical conclusions. There is no delivered Reg mirror or validated registration. [#16351](https://github.com/the-omega-institute/trureturing/issues/16351) identifies the missing dependent-family reconstruction, exact bridge, enrolled readout, observational-dependence evidence, and variation and sensitivity proofs.

The public cyclic evaluation helper `D5.S3.Quantum.Algebra.GeneralizedCHSHGroupDecomposition.cyclicHom_int` is consumed by this proof and by the encoder settlement in #19189. Its four-slot audit is unfinished under [#19215](https://github.com/the-omega-institute/trureturing/issues/19215), which identifies the missing dependent-family realization, reconstruction and equivalence bridges, enrolled readout, variation, sensitivity and observational dependence. No validated registration is claimed for this helper.

## Triage

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| A commuting normal subgroup isomorphic to $L_n$, generated by the images of $P_0^iP_1^{-i}$ | **Proved.** Kernel-checked `delta_commute` and `K_isMulCommutative` establish commutation; `result`, `forward_ks`, `backL_t` and the inverse identities supply the factor identification. Normality and equality with the generated subgroup follow by the prose derivation below. |
| $s=P_1P_0^{-1}$ has order $2n$, and $s^2=J$ | **Proved.** Kernel-checked `ks_coe`, `ks_square_z`, `backL_s` and `forward_backward` identify the element and its square. Exact order is the prose consequence of the factor identification below; `ks_order` alone states the upper bound. |
| $t_{n-1}=s^nt_1\cdots t_{n-2}$ supplies cyclic wrap-around | **Proved, kernel-checked.** `u_last`, `prod_e`, `step_e_last`, `step_e` and `step_period` establish the endpoint and period identities used to construct `alpha`. |
| Odd-$n$ simplification $G_n\cong C_n\times(V_n\rtimes C_n)$, with $V_n$ the even-weight subspace of $C_2^n$ | **Open.** Neither formalized nor computed by the experiment. The source gives $G_3\cong\mathbb Z_3\times A_4$; no uniform simplified-form settlement is claimed. |
| Correspondence with the authors' $G_4$ and $G_6$ forms | **Open** for the explicit isomorphisms. **Computed** only for the orders $128$ and $1152$ in the pinned experiment. |
| Exact finite readings | **Computed** for $n=2,\ldots,9$ by the experiment entry in Evidence; no wider computational scope is claimed. |
| Literature screen | No all-$n$ product decomposition was found in the screened citing works and later author papers recorded in #16204. Completeness is **ASSUMED-UNVERIFIED**; the Firecrawl Google Scholar query returned HTTP 402. |

For the first item, let $F$ be the forward equivalence used by `result`, and let $K$ be the subgroup generated by all $\delta_i$. Each $F(\delta_i)$ has trivial outer cyclic coordinate, so $F(K)$ lies in the copy of $L_n$. Conversely, `ks_coe` and `forward_ks` identify preimages of $s$ and each $e_i$ inside $K$; `backL_t` identifies preimages of every independent $t_i$ there. These elements generate $L_n$, so $F(K)=L_n$. This copy is the kernel of the projection to $C_n$, hence normal; restricting $F$ gives $K\cong L_n$. This is a derivation from the constructed maps, not a separate Lean normality declaration.

For the second item, `ks_coe` at zero identifies $P_1P_0^{-1}$ and `ks_square_z` gives its square $J$. Under $F$ it is $(1,1)$ in multiplicative notation in $C_{2n}\times C_2^{n-2}$, where the first component is the additive residue $1$ modulo $2n$. That residue has exact order $2n$, and isomorphisms preserve order. The exact-order assertion here is derived in prose; the module's private `ks_order` verifies its $2n$-th power is one.

The decisive mechanism is the uniform cyclic orbit together with mutually inverse generator maps. It covers every $n\ge2$, including the empty independent-involution factor at $n=2$. The source's presentation and Theorem 5.7 remain applicable; its strategies and order computation require no replacement. The neighbouring odd and even classifications above are additional questions, rather than prerequisites of this equivalence.

## ASSUMED-UNVERIFIED

The citation-index and later-author screens are not an exhaustive literature proof. Their producer and scope are recorded in #16204; a Firecrawl Google Scholar query returned HTTP 402. No originality or exhaustive absence claim follows from that screen.

The four-slot escape audit remains unfinished under #16351. Its issue link supplies disclosure, not a registration proof. The uniform odd-$n$ simplification and the explicit $G_4,G_6$ correspondences are not established by this delivery.
