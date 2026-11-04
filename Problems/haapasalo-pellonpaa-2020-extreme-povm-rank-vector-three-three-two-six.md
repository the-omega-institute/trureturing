---
slug: haapasalo-pellonpaa-2020-extreme-povm-rank-vector-three-three-two-six
bibkey: haapasalopellonpaa2020extreme
doi: 10.1088/1751-8121/ab8d52
url: https://arxiv.org/abs/1809.09935v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/ExtremePOVMRankThreeThreeTwoSix.result
---

# The rank vector $(3_2,2_6)_7$ is realized by an extreme POVM

## Problem

E. Haapasalo and J.-P. Pellonpää, *Effective methods for constructing extreme quantum observables*, arXiv:1809.09935v1 (J. Phys. A: Math. Theor. 53, 245301 (2020)), define finite-outcome POVMs as tuples of positive operators summing to the identity and define extremality by the midpoint condition (source TeX `laatikkopaperi_v4.tex`, lines 139 and 148–152). They order rank vectors and omit rank-one outcomes (lines 219–222). Their low-dimensional discussion says:

> In dimensions 1-4, we are able to completely characterize the possible rank vectors of extreme POVMs but in dimensions 5-7 some open questions remain. (line 307)

and, for dimension seven,

> The new problematic case now is $(3_2,2_6)_7$. (line 314)

The formal question is whether there is an extreme POVM on $\mathbb C^7$ whose rank-at-least-two multiset is two 3s and six 2s. The module's `claim` states that every `n` and every family $M:\operatorname{Fin}(n)\to\operatorname{Matrix}(\operatorname{Fin}(7),\operatorname{Fin}(7),\mathbb C)$ satisfying `IsPOVM M` and `IsExtreme M` has `bigRanks M` different from $\{3,3,2,2,2,2,2,2\}$. The declaration `result` has type $\lnot\claim$.

## Motivation

The source presents ranks as a resource measure for implementing an extreme observable and asks which rank combinations can occur. Resolving $(3_2,2_6)_7$ supplies the missing seven-dimensional instance and tests the source's necessary rank conditions at the first unresolved case named there.

## Gap

The preregistration issue [#23811](https://github.com/the-omega-institute/trureturing/issues/23811) records the bounded literature check. The v1 preprint identifies the case as open. O. Schmidt, *Reduction and extremality of finite observables*, arXiv:1903.12000, leaves the general rank problem open in the TeX passage at lines 966–970 and does not settle this seven-dimensional case. The citing works searched in #23811 do not report a settlement of $(3_2,2_6)_7$, and the repository search found no prior D5 treatment of this question. The journal landing page was not independently readable from the host, so the check is `not-found-in-searched-scope`.

## Route

1. In the ordered coordinates $(e_0,e_1,e_2,f_0,f_1,f_2,g)$, the private `blocks` definition gives
   \[
   \begin{aligned}
   B_0&=(e_0,e_1,e_2),& B_1&=(f_0,f_1,f_2),\\
   B_2&=(e_0+f_0,e_1+f_1),& B_3&=(e_0+i f_0,e_1+i f_1),\\
   B_4&=(e_0+f_0+g,e_2+f_2),& B_5&=(e_0+i f_0+g,e_2+i f_2),\\
   B_6&=(e_1+f_1+g,e_2+f_2+g),&
   B_7&=(e_1+i f_1+g,e_2+i f_2+g).
   \end{aligned}
   \]
   The private `effect` is $\sum_{b\in B_j}bb^\ast$ and `frame` is the sum of the eight effects. The hypothesis-free theorem `frame_posDef` proves `frame.PosDef` by an exact coordinate calculation. The hypothesis-free `normalizer_exists` then gives a matrix $R$ with `IsUnit R.det` and $R\,\mathrm{frame}\,R^\ast=1$; `normalizer`, `normalizer_unit`, and `normalizer_identity` select and record this choice. The private `witness` is $R\,\mathrm{effect}_j\,R^\ast$.
2. Theorems `effect_posSemidef` and `witness_posSemidef` prove positive semidefiniteness for each index $j:\operatorname{Fin}(8)$, and `witness_sum` proves that the eight witnesses sum to $1$. Thus `witness_povm` proves `IsPOVM witness`. For each $j:\operatorname{Fin}(8)$, `left_columns` proves `left j * columns j = 1`, `effect_columns` proves `effect j = columns j * (columns j)ᴴ`, `effect_rank` proves `(effect j).rank = (blocks j).card`, and `witness_rank` proves `(witness j).rank = (effect j).rank`. The hypothesis-free theorem `witness_bigRanks` consequently proves `bigRanks witness = \{3,3,2,2,2,2,2,2\}`.
3. The hypothesis-free theorem `within_block_product_independent` proves linear independence over $\mathbb C$ of
   \[
   p\longmapsto \operatorname{vecMulVec}(p.2.1.1,(p.2.2.1)^\ast)
   \]
   indexed by $p:\sum_{j:\operatorname{Fin}(8)}(\operatorname{blocks}(j)\times\operatorname{blocks}(j))$. The hypothesis-free `normalizeMap_ker` proves that multiplication on the left by the selected normalizer and on the right by its adjoint has trivial kernel. The hypothesis-free `normalized_product_independent` transports the preceding independence to the normalized products. For every $j:\operatorname{Fin}(8)$ and every $x:\operatorname{Matrix}(\operatorname{blocks}(j),\operatorname{blocks}(j),\mathbb C)$, `normalized_expansion` gives the exact expansion of $(R\,\mathrm{columns}_j)x(R\,\mathrm{columns}_j)^\ast$ in those normalized products.
4. The private lemma `supported_decomposition` has the following exact hypotheses: a finite type $\iota$ with decidable equality; $u:\operatorname{Matrix}(\operatorname{Fin}(7),\iota,\mathbb C)$; $w:\operatorname{Matrix}(\iota,\operatorname{Fin}(7),\mathbb C)$; $w u=1$; matrices $a,b$ of size $7$ by $7$; $a.\operatorname{PosSemidef}$; $b.\operatorname{PosSemidef}$; and $u u^\ast=\tfrac12\,(a+b)$. Its conclusion is
   \[
   a-u u^\ast=u\bigl(w(a-u u^\ast)w^\ast\bigr)u^\ast.
   \]
   In `decomposition_eq_of_product_independence`, for $A,B:\operatorname{Fin}(8)\to\operatorname{Matrix}(\operatorname{Fin}(7),\operatorname{Fin}(7),\mathbb C)$, hypotheses `hA : IsPOVM A`, `hB : IsPOVM B`, and $\forall j,\ \mathrm{witness}\ j=\tfrac12(Aj+Bj)$ imply $A=\mathrm{witness}\land B=\mathrm{witness}$. It applies `supported_decomposition` with the two POVM positivity hypotheses, uses `normalized_expansion`, sums the differences to zero using the two POVM normalization equations, and applies `normalized_product_independent`. The hypothesis-free `witness_extreme` packages `witness_povm` and this decomposition theorem into `IsExtreme witness`.
5. The result proof assumes `claim` and applies it at $n=8$ to `witness`, using `witness_povm`, `witness_extreme`, and `witness_bigRanks`. This derives the contradiction and proves `result : \lnot claim`.

## Falsifier

The settlement would not address the source question if the formal rank predicate or midpoint predicate changed its quantifiers. Here `IsPOVM` is exactly positive semidefiniteness of every effect together with sum equal to the identity; `IsExtreme` requires that predicate and says that every midpoint decomposition into two such POVMs has both factors equal to the original family. The formal `bigRanks` is the multiset of the effect ranks after filtering to ranks $r$ with $2\le r$, so it discards ranks zero and one and does not impose an ordering; equality with the target multiset is therefore the precise formal version used by `claim`. The result's witness has eight outcomes on $\mathbb C^7$ and the exact target multiset, so a numerical check on a different family would not establish this refutation.

## Evidence

The canonical source is `D5/S3/Quantum/Measurement/ExtremePOVMRankThreeThreeTwoSix.lean`.
Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurement/ExtremePOVMRankThreeThreeTwoSix.lean.json`.

Declaration statements:
- `result`: `sha256:b2bfd0abc1e96a33e170372c86d974628ae9f4bad66f30f4bcdce3a17a2db4f1`;
- `claim`: `sha256:d53dec926ea0f24884b3e8d109aee355c2d3a9bc27e84c3a4e9ce6b09b558585`.

- **Proof.** It proves `result : ¬ claim` by applying `claim` at $n=8$ to the private `witness`, with `witness_povm`, `witness_extreme`, and `witness_bigRanks`.
- **Axioms.** `#print axioms result` reports `propext`, `Classical.choice`, and `Quot.sound`; the module has no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 open problem in a 2018 preprint, published in 2020, preregistered in issue #23811 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** An eight-outcome family `witness` of $7$ by $7$ complex matrices is a POVM, is extreme under the module's midpoint definition, and has `bigRanks witness = \{3,3,2,2,2,2,2,2\}`; therefore the universally quantified exclusion in `claim` is false.

**Computed, not formalized** (orchestrator, recorded in #23811): the target rank vector $(3,3,2,2,2,2,2,2)$ satisfies the source's necessary rank conditions.

**Argued, not formalized.**
- **Mechanism.** The two phase choices on each coordinate edge separate cross coefficients, the apex coordinate $g$ separates the remaining diagonal coefficients, and the two coordinate blocks remove the residual coefficients. Under the exact hypotheses of `decomposition_eq_of_product_independence`—`hA : IsPOVM A`, `hB : IsPOVM B`, and `hmid : ∀ j, witness j = (1 / 2 : ℂ) • (A j + B j)`—the normalized within-block products are independent; `supported_decomposition` confines each difference $A_j-\mathrm{witness}_j$ to their span, and `decomposition_eq_of_product_independence` uses the normalization sum to force every coefficient to vanish. This explains why the finite construction defeats the universal exclusion.
- **Scope.** The refutation supplies one eight-outcome POVM in dimension seven. It does not settle the source's general sufficiency question for conditions (i)–(iii), the separate cases $(3,2_4)_5$ and $(3_2,2_3)_6$, or the packing-problem characterization.
- **Effect on the source.** The sentence identifying $(3_2,2_6)_7$ as the new problematic dimension-seven case is resolved by this instance. Statements about the other rank vectors and about general rank-vector sufficiency are not settled by this module; no source theorem depending on a universal exclusion of this vector is established here.

## ASSUMED-UNVERIFIED

The literature check is bounded and does not establish exhaustive worldwide novelty or priority. The 2020 journal version was not independently readable from the host, and the citation search recorded in #23811 was not a complete survey. The rank conditions in “Computed, not formalized” and the mechanism and scope statements in “Argued, not formalized” are not additional Lean declarations. General sufficiency beyond the exact counterexample, the dimension-five and dimension-six cases named above, and any stronger packing characterization are not addressed by this module.
