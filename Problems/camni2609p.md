---
slug: camni2609p
bibkey: camargo2026gaussianmultientropy
doi: 10.48550/arXiv.2609.30754
url: https://arxiv.org/abs/2609.30754v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/GaussianStates/PageMultiEntropyLargeN.result
---

# Page and multi-entropy large-mode formulas at replica order three

## Problem

Hugo A. Camargo and Mitsuhiro Nishida, *Genuine Multi-Entropy of Fully Symmetric Gaussian States*, arXiv:2609.30754v2, §6 after equations (63)–(64), asks:

> It would be very interesting to obtain similar analytic formulas for the subsystem configurations corresponding to the Page and Multi-entropy times in the large $N$ regime. This would be particularly important to determine the behavior of $\mathrm{GM}_{3}^{\mathtt{3}}$ in other relevant subsystem configurations.

Write $G(a;A,B,C)$ for the source's normalized Gaussian replica-integral quantity at replica order three and $d=a^2-1$. The answer is that for each real $a>1$ there is one $K>0$ such that every positive natural $k$ satisfies both

$$
\left|G(a;2k,k,k)+\frac1{12}\log(4kd)-\frac1{12}\log\frac{400}{27}\right|\le\frac K{4k},\qquad
\left|G(a;k,k,k)+\frac1{12}\log(3kd)-\frac1{12}\log\frac{27}{2}\right|\le\frac K{3k}.
$$

### Statement echo

| Source clause or quantified convention | Lean counterpart | Fidelity |
| --- | --- | --- |
| Fully symmetric Gaussian states and normalized replica contraction | Existing `GaussianMultiEntropyAsymptotic.GM3` | The integral-defined source object is retained. |
| Replica order three | First argument `3` of `GM3` | No replica continuation. |
| Page configuration under equal outgoing subsystems | Sizes $(2k,k,k)$ and total $N=4k$ | Every positive multiple of four is covered. |
| Multi-entropy configuration | Sizes $(k,k,k)$ and total $N=3k$ | Every positive multiple of three is covered. |
| Large $N$ at fixed squeezing | Universal real $a>1$, then existential real $K>0$, then universal positive natural $k$ | $K$ may depend on $a$ and is shared by both sequences. |
| Analytic formulas | The two absolute logarithmic error bounds in `claim` and `result` | The constants are derived answer coefficients, not conjectured source coefficients. |
| Additional binders or conjuncts | None beyond this quantified nominated answer | No determinant identity or certificate is assumed. |

The only new public definition is `PageMultiEntropyLargeN.claim`. Its body is literally the quantified nominated answer preregistered in [#22644](https://github.com/the-omega-institute/trureturing/issues/22644). The source asks for analytic formulas without specifying their coefficients. The displayed bounds supply such formulas; they do not reinterpret the source as a conjecture of these constants.

## Motivation

The settling GID is `D5/S3/Quantum/GaussianStates/PageMultiEntropyLargeN.result`. Its admission basis is `open-problem-resolution (#22644; Proved)`, with generality `G` and utility `none`. All authored proofs are bind-only after expansion against existing frozen owners and pinned Mathlib; the five private helpers have live consumers. There is one delivered Lean module and no supporting first freeze, atom or cover.

## Gap

The result covers fixed $a>1$ and the two positive integer sequences above. It supplies neither a uniform estimate as $a\downarrow1$ nor formulas for all replica orders or nonsymmetric Gaussian states.

The escape audit of `D5.S3.Quantum.GaussianStates.PageMultiEntropyLargeN.result` is unfinished under [#22846](https://github.com/the-omega-institute/trureturing/issues/22846). A faithful dependent-family registration still needs the exact Gaussian-operand reconstruction, the shared-$K$ equivalence bridge, whole-family variation and sensitivity, and actual observational dependence. No Reg mirror or validated registration is delivered.

## Route

The proof applies the frozen `ReplicaThree.GM3_three_closed` to every positive integer tripartition at $a\ge1$, and uses the frozen `ResidualLimit.GM3_eq_fourierGM` bridge. These are existing results on the proof dependency path. With $N=A+B+C$ and $u=3d/(4(N-1))$, they give

$$
G(a;A,B,C)=\frac1{12}\log\frac{[1+u(AB+AC+BC)]^2}{[1+uA(B+C)][1+uB(A+C)][1+uC(A+B)]}.
$$

The private `finite_gm` adapts exactly this owner statement. Substitution yields $z_P=3dN^2/(64(N-1))$ for the Page sequence and $z_M=dN^2/(12(N-1))$ for the equal sequence. Factoring the logarithms yields

$$
12E_P=\log(1-1/N)+2\log(1+1/(5z_P))-\log(1+1/(4z_P))-2\log(1+1/(3z_P)),
$$
$$
12E_M=\log(1-1/N)+2\log(1+1/(3z_M))-3\log(1+1/(2z_M)).
$$

The private `abs_log_add_le` and `abs_log_sub_inv_le` apply Mathlib's `Real.log_le_sub_one_of_pos` and logarithm sign rules. They bound the correction terms by $h$ for $\log(1+h)$ and by $2/N$ for $\log(1-1/N)$ when $N\ge2$. Rational normalization and these bounds in `page_error` and `me_error` give the common positive choice

$$K=\frac{2+30/(a^2-1)}{12}.$$

## Falsifier

A real $a>1$ for which no positive $K$ bounds both displayed error sequences for all positive natural $k$ would refute `claim`. A finite numerical agreement cannot establish that quantified assertion. Replica orders other than three, zero-size parties and a uniform limit at $a=1$ are outside it.

## Evidence

The kernel-checked settling declaration is `D5.S3.Quantum.GaussianStates.PageMultiEntropyLargeN.result`. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}. Its Scribe node displays the full claim and carries one Proved `OpenProblemResolutionClaim`. The source note is `Library/Entropy/camargo2026gaussianmultientropy.md`.

Experiment: [exact finite checker](https://github.com/the-omega-institute/trureturing-experiments/tree/25a25360d7d48a4ea64a38b84e690178dba8db47/docs/reports/camargo-nishida-page-multientropy-large-n). The script at that immutable revision is `check.py`, SHA-256 `4f6007098b18042fc8e4231e28e55428cf6c67a4ab1a73b500ebc6c5d2d3fe88`. Command: `python3 /tmp/op-camni2609p/stage-b/experiment-check.py`, using the exact bytes extracted from that revision; exit 0. It verifies 336 reduced matrices for all ordered positive tripartitions with $3\le N\le9$ and $r\in\{1,1/2,1/3,1/5\}$; 10 full Gaussian precision matrices for $3\le N\le5$ at $r=1/2$; 160 Page/ME algebraic configurations at $d\in\{1/10,1,3,15\}$; 12 source-table instances across the triples $(1,1,1),(2,1,1),(3,1,1)$; and the $a=1$ algebraic boundary. These are finite exact checks, not uniform analytic estimates.

## Triage

| Item | Status | Evidence |
| --- | --- | --- |
| Constant mode and four paired character classes; radical and powers of $r$ cancel | Proved, reused kernel-checked results | `ReplicaThree.GM3_three_closed`, through its nine-character product calculation and `ResidualLimit.GM3_eq_fourierGM`; the integral bridge incorporates `ResidualLimit.epsilon_identity`. These are prior owner results rather than new content claims. |
| Finite identity for positive tripartitions and $a\ge1$; both fixed-$a$ estimates for every permitted positive $N$ | Proved | The finite identity is the exact statement of existing `ReplicaThree.GM3_three_closed`, adapted by private `finite_gm`; the two quantified estimates are `PageMultiEntropyLargeN.result`, using private `page_error` and `me_error`. |
| 336 reduced matrices, 10 full precision matrices, 160 Page/ME configurations, 12 table instances, and $a=1$ | Computed | The immutable checker, command, exit code and SHA-256 in Evidence; only the stated finite scope is tested. |
| Replica orders $n\ge4$, nonsymmetric states, and the separate upstream $n=2,q=3$ vanishing theorem | Open as extensions of this settlement | No delivered statement establishes the first two. The upstream vanishing result is separate and is not asserted as a consequence here. |
| Uniformity as $a$ approaches one | Open | The displayed sufficient $K$ diverges as $a\downarrow1$; this does not prove that every uniform formulation fails. |
| The $n=2,q\ge4$ factorization problem #22629 | Open | Outside the delivered claim. |
| Literature status | Literature reading | #22644 screens v2, arXiv and author records, INSPIRE, Crossref, citing works and relevant Gaussian papers. The general Fourier/integral method and finite formula have existing owners; no Page/ME large-$N$ settlement was found in that searched scope. Completeness is ASSUMED-UNVERIFIED. |

### What the settlement shows

The decisive mechanism for the two bounds is cancellation of the leading powers in the existing finite formula, followed by elementary logarithm estimates. The character decomposition underlying that formula has one constant mode and four paired classes. In the source scalar representation, writing $r=s/t$ gives $N^2(a^2-1)=(N-1)(1-r)^2/r$; this is an explanation of the existing radical cancellation, not an additional theorem delivered here.

The finite identity extends over every positive integer tripartition at $a\ge1$. The requested estimates extend over every allowed positive total mode count at each fixed $a>1$, with the same $K$ for both sequences. No sharpness of $K$ or uniformity at vacuum is claimed. The source's illustrative total $N=24$ is not a restriction on the result. The answer supplies the requested order-three Page and Multi-entropy asymptotics; it leaves the source's other replica orders, nonsymmetric-state questions and #22629 unchanged in scope.

## ASSUMED-UNVERIFIED

The completeness of the literature census and global novelty are ASSUMED-UNVERIFIED. The preregistration reports rate limits at OpenAlex and Semantic Scholar, partial arXiv API access and an unread MathDB solutions count; inaccessible searches are not negative results. The exact checker has only its stated finite scope. A faithful four-slot escape registration remains unfinished under #22846.
