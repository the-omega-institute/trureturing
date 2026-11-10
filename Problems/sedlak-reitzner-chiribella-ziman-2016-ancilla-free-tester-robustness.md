---
slug: sedlak-reitzner-chiribella-ziman-2016-ancilla-free-tester-robustness
bibkey: sedlakreitznerchiribellaziman2016testers
doi: 10.1103/PhysRevA.93.052323
url: https://arxiv.org/abs/1511.00976v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/AncillaFreeTesterRobustnessEquality.result
---

# Ancilla-free testers with a common normalization state have canonical POVM robustness

## Problem

M. Sedlák, D. Reitzner, G. Chiribella and M. Ziman, *Incompatible measurements on quantum causal networks*, Phys. Rev. A 93, 052323 (2016), arXiv:1511.00976v2, Section VI.C, ask (verbatim from `ti_pra_07.tex`, line 807, retaining the source's TeX macros):

> It is an open question whether  the equality $\Rt({\st A},  {\st B})  =  \Rm(  \st P,  \st Q )$ holds for all ancilla-free testers.

Here $R_{\rm t}$ and $R_{\rm m}$ denote tester and measurement robustness. Section VI restricts attention to testers with the same normalization state (`ti_pra_07.tex`, lines 758 and 772); that hypothesis is retained. Proposition 3 characterizes ancilla-free testers as $T_a=M_a\otimes\rho$ for an output POVM $M$ and an input density matrix $\rho$ (lines 333–338). Definitions and locators are in [the literature note](../Library/Observer/sedlakreitznerchiribellaziman2016testers.md).

Issue [#23653](https://github.com/the-omega-institute/trureturing/issues/23653) fixes the following finite-dimensional reading. Let $y,x,j,k$ be finite types with decidable equality, indexing output coordinates, input coordinates and the two outcome sets. Let $\rho$ be a complex matrix on $x$ with $\rho\succeq0$ and $\operatorname{Tr}\rho=1$. Let $M=(M_a)_{a\in j}$ and $N=(N_b)_{b\in k}$ be complex output POVMs: each effect is positive semidefinite and each family sums to $I_y$. With $r=\operatorname{rank}\rho$, the statement is

$$
R_{\rm t}\bigl((M_a\otimes\rho)_a,(N_b\otimes\rho)_b\bigr)
=R_{\rm m}\bigl((M_a\otimes I_r)_a,(N_b\otimes I_r)_b\bigr).
$$

In the module, `IsTester` means positive semidefinite effects summing to $I_y\otimes\sigma$ for some positive semidefinite $\sigma$ of trace one. `TesterCompatibleAt` at a real $\lambda$ requires noise testers $E,F$ and a joint tester $C$ with

$$
\sum_b C_{ab}=(1-\lambda)A_a+\lambda E_a,
\qquad
\sum_a C_{ab}=(1-\lambda)B_b+\lambda F_b.
$$

The noises have separate existential witnesses; their normalization states are not prescribed to equal $\rho$, and their effects need not be products. `POVMCompatibleAt` uses the same marginal equations with noise POVMs and a joint POVM, each positive semidefinite and summing to the identity. `testerRobustness` and `povmRobustness` are the real infima of their respective feasible $\lambda\in[0,1]$. The source uses minima; attainment is not part of `claim` or `result`. The displayed equality, with these infimum definitions and $I_r$ indexed by `Fin ρ.rank`, is proved.

## Motivation

For a common normalization state, the question isolates incompatibility arising from the measurements. Proposition 15 gives an upper bound by canonical POVM robustness, and Proposition 16 gives equality for a common pure normalization state (`ti_pra_07.tex`, lines 776–805). The question asks whether mixed normalization states also give equality throughout the ancilla-free class. Its resolution determines whether allowing arbitrary tester noise can reduce the required mixing parameter below that of the associated output measurements.

## Gap

The bounded literature check in #23653 reports:

- the orchestrator screened the 16 citing titles listed by INSPIRE (Crossref listed 13) and searched the TeX of arXiv:2405.20080, arXiv:1906.09206, arXiv:1608.01794 and arXiv:2606.23647 without finding a settlement of this question;
- the orchestrator's arXiv abstract searches for ancilla-free testers and tester incompatibility returned only the source and Ragini–Sazim, arXiv:2405.20080;
- GPT Pro reported searches of Zenodo, ResearchGate, SSRN and GitHub without finding a settlement;
- the orchestrator's repository check found no tester-robustness definition and identified existing partial-trace lemmas for reuse.

These are attributed search results from the preregistration, not an exhaustive novelty claim. `not-found-in-searched-scope`.

## Route

All matrix families below have finite coordinate and outcome types; the output type has decidable equality. The main statement additionally supplies decidable equality on all four types. The compatibility predicates themselves allow every real $\lambda$.

1. **Tensoring POVM witnesses.** For a density matrix $\rho$, arbitrary output matrix families $M,N$ and any real $\lambda$, `povm_to_tester_compatible` takes a witness of `POVMCompatibleAt λ M N` to a witness of tester compatibility for $M\otimes\rho,N\otimes\rho$. Its helper `povm_tensor_tester` requires that $\rho$ is a density matrix and that the family being tensored is a POVM. Positivity of Kronecker products and the identity sum give the required testers.
2. **Retracting arbitrary tester witnesses.** For a density matrix $\rho$, arbitrary output matrix families $M,N$ and any real $\lambda$, `tester_to_povm_compatible` takes tester compatibility of $M\otimes\rho,N\otimes\rho$ to `POVMCompatibleAt λ M N`. It traces out $x$ in both noises and the joint tester. For any family satisfying `IsTester`, `tester_partialTrace_povm` gives a POVM, since its normalization state $\sigma$ has trace one. The marginal equations reduce to the output equations because $\operatorname{Tr}_{x}(X\otimes\rho)=X$. No product form or prescribed normalization is assumed for the witness testers.
3. **Removing the canonical identity factor.** For any natural $r$, arbitrary output families $M,N$ and any real $\lambda$, `povm_to_ancilla_compatible` tensors a POVM compatibility witness with $I_r$. Conversely, `ancilla_to_povm_compatible` requires $0<r$ and a compatibility witness for $M\otimes I_r,N\otimes I_r$; it compresses each witness effect to coordinates $(b,0)$. Its helper `compression_povm` requires $0<r$, decidable equality on $y$, a finite outcome type and a POVM on $y\times\mathrm{Fin}\,r$. Positivity and the identity sum survive compression. The public theorem `rank_pos_of_trace_one` supplies $0<\operatorname{rank}\rho$ for every finite-input matrix of trace one; the module `D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation` applies the same theorem.
4. **Equal feasible sets.** `tester_feasible_eq` requires a density matrix $\rho$ and arbitrary output families $M,N$; `ancilla_feasible_eq` requires $0<r$ and arbitrary output families $M,N$. Together they identify the three sets of feasible weights in $[0,1]$. `result : claim` applies these equalities with $r=\operatorname{rank}\rho$ and takes `sInf` of equal sets. This uses no claim about minimizers or numerical bounds on the infima.

## Falsifier

The settlement would miss the source question if it restricted the noise to product testers, silently fixed its normalization to $\rho$, compared only a noncanonical implementation, or dropped the common-state hypothesis. `TesterCompatibleAt` quantifies over arbitrary noise and joint testers. Both original testers use the same $\rho$. The right side uses $M_a\otimes I_r,N_b\otimes I_r$ on the support coordinates, as the canonical POVM definition prescribes for product effects.

That last identification is a mathematical reading of the source, rather than a separately formalized inverse-square-root construction: on $\operatorname{supp}\rho$, conjugating $M_a\otimes\rho$ by $I_y\otimes\rho^{-1/2}$ gives $M_a\otimes I$. The module directly defines the support-coordinate families. It proves equality of infima by equality of sets, rather than deriving an inequality from `sInf` without existence or boundedness premises. Neither attainment nor a robustness bound is asserted by `result`.

## Evidence

The canonical source is `D5/S3/Quantum/QuantumChannels/AncillaFreeTesterRobustnessEquality.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/QuantumChannels/AncillaFreeTesterRobustnessEquality.lean.json`.

Declaration statements:

- `result`: `sha256:1db5dc4c303625b28e7e9578b4e20b1b2752dfd92bfb9e30d1adfe0e5a62eb84`;
- `claim`: `sha256:4e73b75e4da884fc0fdb85f3b92df71b1c9c81079f92a9898cc1c97305819135`.

## Triage

Tier 1: an explicit open question in a 2016 paper, preregistered in issue #23653 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for all finite output, input and outcome types with decidable equality, every input density matrix $\rho$ and every pair of output POVMs $M,N$, the infimum tester robustness of $(M_a\otimes\rho)_a,(N_b\otimes\rho)_b$ equals the infimum POVM robustness of $(M_a\otimes I_r)_a,(N_b\otimes I_r)_b$ on the output times `Fin ρ.rank`, where $r=\operatorname{rank}\rho$.

**Computed, not formalized.** No numerical computations are reported.

**Argued, not formalized.**

- *Decisive mechanism.* A compatibility witness cannot gain a smaller feasible mixing parameter merely by using general tester effects: for a finite-input density matrix $\rho$, finite output and outcome types with decidable output equality, arbitrary output families $M,N$ and any real $\lambda$, `tester_to_povm_compatible` retracts every such tester witness to a POVM witness. The reverse map has the same hypotheses in `povm_to_tester_compatible`. Thus the argument compares actual feasible witnesses, not only their optimum values.
- *Scope beyond purity.* For the same finite types and density hypothesis, `tester_feasible_eq` identifies the feasible sets for product testers and the output families without requiring those output families to be POVMs. Their POVM hypotheses in `claim` give the physical interpretation. For any finite output and outcome types with decidable output equality, arbitrary output families and every positive integer $r$, `ancilla_feasible_eq` also identifies output and identity-extended feasible sets. These helper statements explain why purity can be removed and why the identity factor supplies no extra mixing advantage; these are not additional conclusions in the type of `result`.
- *Canonical interpretation.* On the support of a positive semidefinite $\rho$, its positive eigenvalues give $\rho^{-1/2}\rho\rho^{-1/2}=I$. The source's conjugation formula therefore yields the support-coordinate families in `claim`. This bridge uses finite-dimensional spectral calculus and is not separately formalized here.
- *Boundary of the witness argument.* A common normalization is essential to the feasible-set identification: take a one-dimensional output, a two-dimensional input and one outcome for each tester, with their sole effects the two distinct coordinate rank-one projections. At $\lambda=0$ no joint tester can have both as its sole marginal, whereas both canonical POVMs are the singleton identity on a one-dimensional support and admit a joint POVM. This argument separates feasible sets without asserting an unformalized bound on their infima.
- *Effect on the paper and nearby questions.* Under this canonical identification and the stated infimum reading, Proposition 15 is an equality on the common-state ancilla-free subclass, and the pure-state case of Proposition 16 is retained. The source presents these propositions with independent proofs, not as consequences of the open question. The equality compares a fixed pair; it does not select a maximizing pair. Thus it does not settle the mutually unbiased basis conjectures in Section VI.B or Appendix G. Equality for arbitrary testers without product effects, different normalization states, multiple time steps or infinite-dimensional systems is not established by `result`. There is no claim of attainment or of a sharp numerical bound.

## ASSUMED-UNVERIFIED

The bounded literature check is the orchestrator's report in #23653; its citation counts, citing-work readings, arXiv searches and repository-search readings were not independently reproduced here. The Zenodo, ResearchGate, SSRN and GitHub searches are GPT Pro reports recorded in that issue. These checks do not establish exhaustive worldwide novelty or priority.

The source quotation, surrounding definitions, Propositions 15–16 and the separate maximality conjectures were checked in the v2 TeX. The interpretation of the support-coordinate POVMs via inverse-square-root conjugation, the physical implementation correspondence and the consequences discussed under "Argued, not formalized" are not separate formal conclusions of `result`. The module does not prove attainment, numerical robustness bounds or the extensions listed there.
