---
slug: tarabunga-frau-haug-tirrito-piroli-2025-shannon-branch-bound
bibkey: tarabunga2025asymmetry
doi: 10.1088/2058-9565/adfd0d
url: https://arxiv.org/abs/2411.05766v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation.result
---

# A three-qubit counterexample to the Shannon branch-and-bound lower bound

## Problem

P. S. Tarabunga, M. Frau, T. Haug, E. Tirrito and L. Piroli, *A nonstabilizerness monotone from stabilizerness asymmetry*, arXiv:2411.05766v1 (2024; Quantum Sci. Technol. 10 (2025) 045026), Section V.C, conjecture following Eq. (69). The source member `draft.tex`, line 782, states verbatim:

> Note that, while we are unable to prove Eq. \eqref{eq:bound_r} for the case $\alpha=1$, we conjecture that the lower bound remains valid, as we have not found any counter-examples.

The label `eq:bound_r` is the inequality at `draft.tex` lines 776–779: for fixed rank-$k$ binary $R$, $\min_{Q',c}S_\alpha(p_{Q',c,R})\ge S_\alpha(q_R)$, stated there for integer $\alpha>1$. The states indexed by the diagonal part of $Q$ and the translation $t$ give the squared-overlap law $p$; $q_R$ uses zero off-diagonal matrix and zero phase vector after replacing the amplitudes of $\psi$ by their absolute values. The definitions and source locators are in [the literature note](../Library/Entropy/tarabunga2025asymmetry.md).

Issue [#24993](https://github.com/the-omega-institute/trureturing/issues/24993) fixes the reading at $k=N=n\ge1$ and $R=I_n$, where the translation quotient has one element. Write $B_n=\mathbb F_2^n$. For every unit vector $\psi:B_n\to\mathbb C$, strictly upper-triangular $Q'\in\mathbb F_2^{n\times n}$ and $c\in B_n$, define

$\phi_d(x)=2^{-n/2}(-1)^{x^\top(\operatorname{diag}d+Q')x}i^{\sum_j\widetilde c_j\widetilde x_j}$,

$p(d)=\left|\sum_{x\in B_n}\overline{\phi_d(x)}\psi(x)\right|^2$, and $q(d)=\left|\sum_{x\in B_n}2^{-n/2}(-1)^{d\cdot x}|\psi(x)|\right|^2$.

Here the quadratic and dot-product exponents of $-1$ are computed in $\mathbb F_2$ and represented by zero or one, whereas each tilde is the natural representative zero or one and the exponent of $i$ is summed in $\mathbb N$. Put $S_1(r)=-\sum_d r(d)\ln r(d)$, with $0\ln0=0$. The module's `claim` asserts $S_1(q)\le S_1(p)$ for every such $n,\psi,Q',c$, with the unit condition $\sum_x|\psi(x)|^2=1$. Its `result` proves the negation. This refutes a subcase of the source's Shannon conjecture.

## Motivation

The basis-minimized stabilizerness asymmetry (BMSA) minimizes measurement entropy over stabilizer bases. The proposed bound supplies the estimate used to discard branches in an exact minimization: a branch whose lower bound exceeds the incumbent value can be skipped. A quantity that exceeds the branch's actual minimum cannot provide that guarantee. At `draft.tex` line 782, the authors explicitly qualify the Shannon computation:

> In the following, we applied the branch and bound method while assuming that the inequality holds for $\alpha=1$.

## Gap

The bounded literature check recorded in #24993 reports:

- the arXiv v1 source states the conjecture; its `draft.tex` has md5 `3972b4e08038d87ddf28211e09c89fdc`, matching the source read here;
- the orchestrator (Claude Code, Opus) searched the TeX of arXiv:2601.07824, arXiv:2610.38401 and arXiv:2504.18098, selected from 19 Semantic Scholar citing records, without finding a proof or counterexample to the Shannon bound;
- the search contributor reported screening accessible citing texts, and the orchestrator's searches for the conjecture sentence found no settlement;
- issue [#19855](https://github.com/the-omega-institute/trureturing/issues/19855) concerns strong monotonicity of the Rényi BMSA, a different question from Eq. (69).

`not-found-in-searched-scope`. The journal text and the completeness of the citation search are not verified here.

## Route

All local lemma names below belong to `StabilizerAsymmetryShannonBoundRefutation`; the witness and its auxiliary lemmas are private.

1. **A normalized state.** `coeff` assigns $v=(1,0,2,-1,1,0,0,1)$ in computational order $000,001,010,011,100,101,110,111$, with coordinate zero most significant, and `witness` is $\psi=v/\sqrt8$. `witness_unit`, with no hypotheses, proves $\sum_x|\psi(x)|^2=1$.
2. **Exact overlaps.** For every $d,x\in B_3$, `overlap_term` and `abs_term` identify the summands at $Q'=0,c=0$ as $(-1)^{x^\top\operatorname{diag}(d)x}v_x/8$ and $(-1)^{x^\top\operatorname{diag}(d)x}|v_x|/8$. They reuse `FourMUBBoundEntanglementRefutation.scale_sq`, the unconditional identity $(\sqrt8)^{-2}=1/8$. For every $d\in B_3$, `overlap_distribution` and `abs_distribution` evaluate the laws, in the same binary order, as $p=(1/4,1/4,0,0,0,1/4,0,1/4)$ and $q=(9/16,1/16,1/16,1/16,1/16,1/16,1/16,1/16)$.
3. **Entropy comparison.** `overlap_entropy` and `abs_entropy`, with no hypotheses, give $S_1(p)=2\ln2$ and $S_1(q)=4\ln2-(9/8)\ln3$. They reuse `OrientationEntropyBalance.sum_entropy_formula`, whose hypotheses are a positive natural total $M$ and natural counts summing to $M$ over a finite set: the applications use four unit counts with $M=4$ and counts $(9,1,1,1,1,1,1,1)$ with $M=16$. `log_gap`, with no hypotheses, gives $9\ln3<16\ln2$ from the upper half of the unconditional `TwoDeletionRunEntropyBounds.logb_three_bounds` and $\ln2>0$. Consequently $S_1(q)>S_1(p)$.
4. **Contradiction.** `result` assumes `claim` and applies it at $n=3$, the unit `witness`, the zero matrix and the zero phase vector. The zero matrix meets `IsStrictUpper` because every entry is zero. The asserted inequality contradicts the two entropy identities and `log_gap`.

## Falsifier

The refutation would not address the source if its amplitudes, exponents, normalization or quantifiers differed. The module uses basis words `Fin n → ZMod 2`, `Matrix.diagonal d + Q'`, the binary quadratic form `Matrix.toQuadraticForm'`, the natural-number exponent of `Complex.I`, complex conjugation on stabilizer amplitudes and `Complex.normSq` on overlaps. `absProb` takes each complex amplitude's norm before forming the zero-phase overlaps. `shannonEntropy` is the finite Shannon sum in nats, including its zero endpoint convention.

The restriction $k=N$, $R=I_N$ is allowed by the source. Its finite set of strictly upper-triangular $Q'$ and binary $c$ is nonempty, containing the zero pair. A lower bound on its minimum must hold for each member, so one violating pair suffices; no computation of the minimizing pair is needed for `result`. The displayed witness laws are nonnegative and each sums to one, so the contradiction does not rely on applying entropy to an unnormalized law.

## Evidence

The canonical source is `D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation.lean`.

- **Proof.** It defines `claim : Prop` and proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:fa94b9098c2a949ac277543a7d4014ef231d571a964e255ed99d24078bfdf389`;
- `claim`: `sha256:5e806183a5aab13b2f505f06279244364442c6594b119b7ed2ebff97a1c615ae`.

## Triage

Tier 1 conjecture of a 2024 preprint published in 2025, preregistered in issue #24993 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that, for every $n\ge1$, every unit complex state on $B_n$, every strictly upper-triangular $Q'$ and every binary $c$, the Shannon entropy of `absProb` is at most that of `overlapProb Q' c` for that state.

**Computed, not formalized:** None.

**Argued, not formalized.**

- *Mechanism.* The witness's $q$ has a larger largest atom than $p$, but it also has a longer nonzero tail: the largest entries are $9/16>1/4$, while the four largest entries sum to $3/4<1$. Thus neither law majorizes the other. The integer-moment comparisons used in Appendix C.1 do not by themselves control Shannon entropy: the integers $\alpha>1$ have no sequence approaching one, so continuity at one supplies no extension from that range.
- *A sufficient structure.* If a particular pair of laws satisfies $p=Dq$ for a doubly stochastic matrix $D$, concavity of $f(t)=-t\ln t$ on $[0,1]$ gives $\sum_i f(p_i)\ge\sum_{i,j}D_{ij}f(q_j)=\sum_j f(q_j)$. Such a mixing relation would suffice for the proposed inequality; the witness excludes it because the mass on any four output coordinates of $Dq$ is at most the sum of the four largest entries of $q$, namely $3/4$, whereas four entries of $p$ sum to one. Establishing it for any proposed restricted family remains open.
- *Dimension.* For a zero-pair counterexample and any additional unit state with nonnegative real amplitudes, the tensor-product Walsh basis and entrywise absolute values factor. Both laws acquire the same product factor $r$, and $S_1(p\otimes r)=S_1(p)+S_1(r)$ follows by expanding the finite Shannon sum, with zero terms contributing zero. The entropy gap therefore persists for every qubit count $N\ge3$. For a full-support example, choosing each added qubit with two unequal strictly positive real amplitudes keeps both Walsh overlaps nonzero. This extension is not a theorem of the module.
- *Positivity shortcut.* Appendix C.2, `draft.tex` line 1180, states: “Finally,  if $\ket{\psi}$ has positive real amplitudes, it is easy to see that the lower bound in Eq. \eqref{eq:bound_r} can be achieved by $Q' = \mathbf{0}^{k \times k}$ and $c=\mathbf{0}^{k}$.” For nonnegative real amplitudes, equality of $p$ and $q$ at the zero pair follows directly from their definitions, but it does not establish a lower bound on every other pair.
- *Effect on the paper.* Section V.C's Shannon pruning rule loses its universal lower-bound guarantee. Figure 1's explicitly conditional computation, and Shannon benchmarks described as exact because they use this rule, require an independent valid bound or verification that no minimizing branch was discarded. No particular plotted value is refuted here. Appendix C.1's integer-$\alpha>1$ bound is a separate statement, and this settlement does not refute it or establish or refute BMSA monotonicity, additivity, or the analytic large-$N$ estimates of Section V.E, which use other bounds. The Shannon bound for every state in the cases $N=1,2$, or on any specified family of Figure 1 inputs, is open in this dossier.

## ASSUMED-UNVERIFIED

The source text checked is arXiv:2411.05766v1, `draft.tex`, md5 `3972b4e08038d87ddf28211e09c89fdc`; the journal text was not read, so preservation of the conjecture in the published text is unverified. Crossref metadata confirms the DOI and journal citation but does not verify the journal's mathematical text. The arXiv version-history completeness, the Semantic Scholar count, the three citing-paper searches and the wider accessible-text screening are reported in #24993 and were not independently reproduced. That bounded check does not establish exhaustive worldwide novelty or priority.

The arguments in “Argued, not formalized” are not formalized. The general tensor-product extension and the proposed mixing criterion as an application to these laws are outside `result`. The source-to-Lean parameter correspondence is a mathematical reading of the source definitions, not a formalization of the TeX. The source's algorithms and plotted data were not rerun; their particular numerical correctness, the cases $k<N$, and the other BMSA claims are not settled by this module.
