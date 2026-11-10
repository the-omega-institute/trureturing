---
slug: keshari-mayassi-prabhakar-nasser-2026-zeta8-faithfulness
bibkey: kesharimayassiprabhakarnasser2026multivirtual
doi: 10.48550/arXiv.2605.13090
url: https://arxiv.org/abs/2605.13090v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Algebra/Knot/MultiVirtualTwinZetaEightFaithfulnessRefutation.result
---

# Universal faithfulness of the eighth multi-virtual twin representation is false

## Problem

Keshari, Mayassi, Prabhakar and Nasser, *Presentations and Representations of the Multi-Virtual Twin Group and Associated Subgroups*, arXiv:2605.13090v1, Question 4.3 (page 17), ask:

> A natural question arises regarding the faithfulness of $\zeta_8$: for $a \neq 0, \pm 1$, is the representation $\zeta_8$ faithful?

The universal affirmative reading quantifies over $k\geq1$, $n\geq3$, $a\in\mathbb C\setminus\{0,1,-1\}$, $b\in\mathbb C^*$ and $y\in(\mathbb C^*)^k$. The prescribed matrices must define a homomorphism into $\mathrm{GL}_n(\mathbb C)$, and every homomorphism with those generator images must be injective. The theorem `result` negates this closed proposition `claim`.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Section 3, relations (11)–(19) | `Equations`, `relators`, `MultiVirtualTwin` | All nine families, with zero-based position $i$ denoting source position $i+1$ and unchanged color indices; equations become $LR^{-1}$ in Mathlib `PresentedGroup`. |
| $k\geq1$, $n\geq3$ | Natural-number binders and their two lower bounds in `claim` | The entire source range is retained. |
| Theorem 4.1(8), the two displayed blocks | `sBlock`, `rhoBlock` | Literal complex entries, including their signs and denominators. |
| Identity padding outside adjacent positions | `localBlock`, `generatorMatrix` | All four block entries and the outside identity, for both generator families. |
| $a\neq0,\pm1$, $b,y_\alpha\neq0$ | Five hypotheses in `claim` | No distinctness, genericity or root-of-unity restriction. |
| The prescribed representation | `IsZetaEight` and the existence conjunct in `claim` | Equality of the underlying matrices at every generator; invertibility belongs to the actual general linear target. |
| Faithful | The injectivity conjunct in `claim` | Every homomorphism with the prescribed images is quantified. |
| Negative answer | `result : ¬ claim` | The existence conjunct supplies a homomorphism at $k=n=3$, $a=2$, $b=1$, $y_\alpha=1$; the same kernel mechanism applies to every parameter choice at $k=n=3$. |

The inlined generator carrier and generator inclusions are the preregistered expressions. The presentation, free group, complex field and general linear group reuse Mathlib constructions. No extra mathematical premise is added. The existence conjunct expresses the source assertion that these matrices give a representation; an independent Lean construction of arbitrary-parameter general-linear homomorphisms is outside this delivery.

## Motivation

The source proves nonfaithfulness for its first seven representation families and for the eighth family when $a\in\{-1,0,1\}$ (Theorem 4.2). Question 4.3 asks about the remaining eighth-family parameters. Three virtual colors on three strands yield a parameter-independent obstruction.

## Gap

Preregistration #26876 fixes the published question, presentation, parameter range and refutation criterion. The source is literature-attested; the settlement is a suspected-novel resolution under `open-problem-resolution (#26876; Refuted)`, with `generality: G` and certified-instance utility under `basis=refutes`.

The literature screen recorded in #26876 found no matching settlement in the sources successfully checked. Nasser–Ocampo, arXiv:2605.31298v1, Proposition 3.4 treats an additional welded quotient and an eighth-family overlap at $a=0$. The representation results in arXiv:2508.04168v1 concern multi-virtual braids; arXiv:2604.19307v1 concerns universal virtual/welded braid presentations. These do not supply the arbitrary-parameter three-color twin conclusion. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

In $M_3VT_3$, let $r_\alpha=\rho_1^\alpha$, $p=r_0r_1$, $q=r_0r_2$, and $w=[p,q]=pqp^{-1}q^{-1}$. Map both real generators to the identity and the three colors at both positions to $(01),(12),(23)$ on four points. The far-relation families have no instances at $n=3$; every remaining relation reduces using the involution equations. This gives a homomorphism from the actual presented group. It sends $w$ to $(02)(13)$, so $w\neq1$.

For every homomorphism with the prescribed matrices,
$$
\zeta_8(p)=\operatorname{diag}(y_1/y_0,y_0/y_1,1),\qquad
\zeta_8(q)=\operatorname{diag}(y_2/y_0,y_0/y_2,1).
$$
These diagonal matrices commute, so $\zeta_8(w)=I_3$. Thus every such homomorphism at $k=n=3$ is noninjective. The negation of the universal assertion specializes its existence and injectivity conjuncts to the permitted values $a=2$, $b=1$, $y_\alpha=1$ and derives a contradiction.

## Falsifier

The refutation requires the actual nine source relation families, a well-defined detecting action with nonidentity image of $w$, and the prescribed diagonal pair products. A mismatch in any of these would invalidate the argument. The private proofs of `color_relators`, `kernelWord_ne_one`, `rho_pair_diagonal`, `zeta_kernel` and `zeta_not_injective` discharge these obligations on the proof path of `result`.

## Evidence

The mathematical source is `D5/S3/Quantum/Algebra/Knot/MultiVirtualTwinZetaEightFaithfulnessRefutation.lean`; its canonical exposition is the corresponding Blueprint Scribe. The only public theorem is `result`; the source definitions and all six private theorem helpers support that result. The helpers and result are classified `bind-only` after expansion; no non-bind-only escape witness is claimed. All private helpers have actual consumers. Admission rests on the external named open-problem-resolution exception, with certified-instance utility for the finite detecting action.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Exact experiment

The experiment is [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/8544220e1a6e808622db40c167046c0015d0d134/docs/reports/keshari-mayassi-prabhakar-nasser-2026-zeta8-faithfulness). Its `check.py` was read from that immutable Git object and run as `python3 /tmp/op-kmpn2605z8/check.py`, exit 0, with terminal result `ALL_CHECKS_OK`. The script SHA-256 is `a62f66fd0aecb192e777802fd081d8b4e6dcc0f464f05d5edb63b1934436d792`. It uses exact symbolic rational-function arithmetic.

The tested source-relation scopes are $(k,n)=(2,3),(3,3),(3,4)$, with respectively $12,20,62$ instances. It also checks the specialized two-color word at $y_1=-y_0$, the independent-symbol three-color diagonal products and commutator identity, the detecting quotient reductions, and the four-point image $(2,3,0,1)$. These are computations; they do not construct the arbitrary-parameter general-linear homomorphisms in Lean.

## Triage

Literature status: no matching settlement was found in the screened sources recorded in #26876; literature completeness and publication priority are `ASSUMED-UNVERIFIED`.

### What the settlement shows

1. **Proved in this module (kernel-checked): mechanism.** `rho_pair_diagonal` gives the two same-position color-pair diagonal products; `zeta_kernel` proves that every prescribed homomorphism kills their commutator. `color_relators` validates the quotient action and `kernelWord_ne_one` detects the source commutator as nonidentity. Diagonal commutation in the image loses a distinction present in the source group.
2. **Proved in this module (kernel-checked): uniformity.** `zeta_not_injective` quantifies over every complex $a,b$ and every $y:\mathrm{Fin}\,3\to\mathbb C$, conditional only on the prescribed homomorphism predicate. It therefore covers every allowed parameter tuple at $k=n=3$. Distinct or generic parameters cannot restore faithfulness for this pair. `result` refutes the universal affirmative reading. Independent existence of the arbitrary-parameter GL homomorphisms is not a delivered Lean theorem.
3. **Computed:** the pinned experiment validates all source matrix relations for $(k,n)=(2,3),(3,3),(3,4)$, respectively $12,20,62$ instances. The experiment entry gives the immutable source, command, exit 0 and SHA-256. These are symbolic relation identities, not a Lean construction of the GL homomorphisms.
4. **Computed:** for $k=2,n=3,y_1=-y_0$, the experiment gives identity matrix image for $(\rho_1^0\rho_1^1)^2$ and nonempty detecting free-product reduction $(0,1,0,1)$. The experiment entry supplies the command, exit 0 and SHA-256. This auxiliary statement is not a delivered Lean theorem.
5. **Open:** generic small-color cases $k=1$ and $k=2$, and the complete parameter classification, are not settled by this proof. The special two-color computation establishes no generic two-color conclusion.
6. **Open:** nontriviality of this same word at other $n$ or $k$ is not separately established. The $n=3$ detecting quotient uses the absence of far relations; the argument does not assert its validity for $n\geq4$. The matrix-relation computation at $(3,4)$ establishes neither source-word nontriviality nor faithfulness there.

The source definitions and its Theorem 4.2 exceptional-parameter conclusions are compatible with this refutation; those source conclusions are literature statements, not separately formalized here. The universal positive answer to Question 4.3 is false. No assertion that every eighth-family representation at every $k,n$ is unfaithful, and no assertion about irreducibility, follows from this delivery. Restricted positive faithfulness statements require their own proofs.

## ASSUMED-UNVERIFIED

Literature completeness and publication priority are `ASSUMED-UNVERIFIED`. The preregistration records incomplete citation indexes: OpenAlex omits a known citing paper, Semantic Scholar returned HTTP 429, general-web challenges gave no usable result set, and MathDB was unverified. The Machina screen used its served older snapshot. Absence from these indexes is not proof that no earlier settlement exists.

An independent Lean construction of arbitrary-parameter GL homomorphisms is not supplied. The formal negative answer uses the existence conjunct of the closed universal claim; the uniform private noninjectivity theorem applies to every actual homomorphism with the prescribed images. The computation and the source representation theorem provide separate evidence at their stated scopes.
