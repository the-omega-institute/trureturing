---
slug: maity-furuichi-dutta-2026-tsallis-ordering-case-5
bibkey: maityfuruichidutta2026deformed
doi: null
url: https://arxiv.org/abs/2607.01805v1
triage: theorem
motivation_gids:
  - D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.result
---

# The Maity–Furuichi–Dutta noncommuting Tsallis bound ordering is false

## Problem

Srikrishna Maity, Shigeru Furuichi and Supriyo Dutta, *r-deformed α-z-Rényi relative entropy*, arXiv:2607.01805v1, equations (8)–(9), printed page 2:

> For 0 ≤ α < 1 and q > (1 − α), we compare two upper bounds B₁(ρ||σ) = D^{(r)}_{α,z}(ρ||σ) and B₂(ρ||σ) = −Tr[ρ ln_{1−α}((ρ^{−q/2} σ^q ρ^{−q/2})^{1/q})] of the Tsallis relative entropy, numerically. We observe that for non-commutative density operators ρ and σ, D_α(ρ||σ) ≤ B₁(ρ||σ) ≤ B₂(ρ||σ).

Section 4, Case 5, printed page 12:

> Let Tr(ρ) = 1 and Tr(σ) = 1, that is both ρ and σ are density operators. Here, we numerically observe that for any two operators ρ and σ, B₁(ρ||σ) is a tighter bound of Tsallis relative entropy than B₂(ρ||σ).

The target is the second inequality, $B_1\le B_2$. [Preregistration #18947](https://github.com/the-omega-institute/trureturing/issues/18947) supplies the source quotations, parameter conventions and literature screen.

### Statement echo

| Source clause | Formal counterpart | Scope |
| --- | --- | --- |
| Definition 1: $\ln_r(x)=(x^r-1)/r$ | `lnr` | The literal real-power expression; $r\ne0$ is imposed by `claim`. |
| Definition 2: $D^{(r)}_{\alpha,z}$ is the deformed logarithm of the trace of the powered sandwich, divided by $\alpha-1$ | `renyiRZ` | The source's $B_1$, using `cfc` and the real trace; no separate forwarding definition. |
| Equation (6): $D_\alpha=\operatorname{Tr}[\rho-\rho^\alpha\sigma^{1-\alpha}]/(1-\alpha)$ | `tsallis` | Literal expression, with real trace. |
| Equations (8), (47): the inverse-power sandwich and negative weighted deformed-log trace | `B2` | Literal $B_2$, including the order of factors. |
| Noncommuting density operators | `claim` quantifies $n$, two complex $n\times n$ matrices, positive definiteness, trace one and noncommutation | Positive definiteness is a sufficient subclass of density operators; it satisfies support and negative-power conditions. Refutation in this subclass refutes the stated assertion. |
| $0\le\alpha<1$, $q>1-\alpha$; Definitions 1–2 give $r\ne0$, $z>0$ | All four real parameters and all five hypotheses in `claim` | The counterexample uses plotted parameters $\alpha=r=1/2$, $z=2$, $q=1$. |
| $D_\alpha\le B_1\le B_2$ | Both conjuncts of `claim` | `result` negates the full conjunction by contradicting its second conjunct. |

## Motivation

The two proposed upper bounds need not have the claimed relative order. Comparing their tightness is distinct from asking whether each bounds the Tsallis relative entropy. The counterexample preserves positive definiteness, unit trace, noncommutation and all parameter conditions.

## Gap

A finite numerical plot does not establish a universal ordering. A single positive definite noncommuting qubit pair with $B_2<B_1$ refutes it.

## Route

Take

$$
\rho=\begin{pmatrix}4/5&0\\0&1/5\end{pmatrix},\qquad
\sigma=\frac1{125}\begin{pmatrix}28&6\sqrt6\\6\sqrt6&97\end{pmatrix},
\qquad \alpha=r=\frac12,\ z=2,\ q=1.
$$

The private proof establishes positive definiteness, trace one and noncommutation. It applies `QuantumTwoPointFunctionalCalculus.two_point_cfc` from `D5/S3/Quantum/Matrix/TwoPointFunctionalCalculus` to the two affine involutions, then evaluates the trace by matrix multiplication and cyclicity. It obtains

$$
B_1=4\left(1-\sqrt{\frac{2117+288\sqrt2}{3125}}\right)>\frac25.
$$

For the second bound,

$$
A=\rho^{-1/2}\sigma\rho^{-1/2}
=\frac1{25}\begin{pmatrix}7&3\sqrt6\\3\sqrt6&97\end{pmatrix},\qquad
\sqrt A=\frac5{\sqrt{154}}(A+I),\qquad
B_2=2-\frac{20}{\sqrt{154}}<\frac25.
$$

These are steps within the proof of `result`, not separate public statements. All supporting lemmas are private and consumed by the settlement.

## Falsifier

The certified strict order $B_2<2/5<B_1$ contradicts $B_1\le B_2$ at the displayed admissible pair. A reversal of either strict inequality or a failure of one of the density or parameter hypotheses would invalidate this counterexample; the Lean proof checks them together.

## Evidence

`D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.result` proves the negation of `claim`. The module's public definitions mirror Definitions 1–2 and equations (6), (8)–(9), (47). The corresponding Blueprint displays the full quantified negation. Its admission basis is `open-problem-resolution (#18947; Refuted)`; its proof shape is bind-only, with no escape witness asserted.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Experiment

[Published numerical check](https://github.com/the-omega-institute/trureturing-experiments/tree/7e01d5f0271284d3b56bec188402ec9657c2fdbf/docs/reports/maity-furuichi-dutta-2026-tsallis-bound-ordering): `python3 check.py`, exit 0; `check.py` SHA-256 `90243c923231b1a9aa7171d85a534e16606b11fe142ef5ecbb1d14dbaad85805`. The computation uses 50-digit mpmath evaluation and SymPy matrix data. At the displayed pair it gives $B_1=0.40495024366381390202$, $B_2=0.38835407194923940310$ and $D_{1/2}=0.384=48/125$, agreeing with the displayed closed forms to the reported digits.

Its rotation-check scope is exactly three eigenvalue pairs $(0.7,0.4)$, $(0.9,0.5)$, $(0.6,0.2)$, each at rotation angles $0.01$ and $0.1$, with $\alpha=r=1/2$, $z=2$, $q=1$. All six satisfy $B_1>B_2$. For the middle pair, $\sigma=I/2$, so both rotations remain commuting; the six checks do not constitute six noncommuting examples. Case 3 is tested only at $\alpha\in\{0.01,0.99\}$, $r=0.7$, $z=2$, $q=1.5$ and the matrices specified in the published program. Three of four printed values agree within $5\cdot10^{-6}$; $B_1$ at $\alpha=0.99$ is $0.2529732$, versus the paper's $0.252861$. These are computed readings, not additional Lean theorems.

## Triage

### What the settlement shows

| Item | Status and evidence | Boundary |
| --- | --- | --- |
| Recommended settlement: Refuted | **Proved (kernel-checked):** `D5.S3.Divergence.MaityFuruichiDuttaOrderingRefutation.result` negates `claim`. | The asserted universal ordering fails. |
| Failed clause: $B_1\le B_2$ at the issue pair and plotted parameters | **Proved (kernel-checked):** `result` uses the private kernel-checked lemmas `B2_lt` and `B1_gt`, which state the exact inequalities $B_2<2/5<B_1$ at the pair in Route. | One noncommuting positive definite qubit pair suffices. |
| Surviving clause: $D_\alpha\le B_1$ | **Open in this module:** the refutation does not negate this inequality separately. | The source's Theorem 1 is literature evidence for its stated domain; no independent Lean proof is delivered here. |
| Implementation scope | **Computed (file inventory):** `git ls-files -- D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.lean Blueprint/D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.scribe.cs Blueprint/D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.md Library/Divergence/maityfuruichidutta2026deformed.md Problems/maity-furuichi-dutta-2026-tsallis-ordering-case-5.md` lists five files (exit 0). The only D5 import is the existing `TwoPointFunctionalCalculus`. | No new generic calculus wrapper or owner publication is delivered. |
| Rotation-check mechanism | **Computed:** the experiment entry verifies $B_1>B_2$ at all six specified rotations, including the two commuting scalar cases stated in Evidence. | A classification or uniform neighbourhood theorem is open in Lean. |
| What survives at the counterexample | **Computed:** the experiment gives $D_{1/2}=48/125<B_2<B_1$. | Both upper bounds hold at this pair; this module proves only the ordering's refutation. |
| Paper's Case 3 comparison | **Computed:** three of four values agree within $5\cdot10^{-6}$, with the fourth discrepancy stated in Evidence. | This finite comparison does not classify other parameters or diagnose the printed discrepancy. |
| Commuting comparison | **Open in this module:** the paper's Theorem 2 states $B_2\le B_1$ for commuting operators. | It is not refuted or formalized here. |
| Consequences for other source results | **Open:** any argument requiring the universal $B_1\le B_2$ needs an additional restriction or a different comparison. | Theorem 1 and equation (46), asserting individual upper bounds, are not refuted; neither is the commuting Theorem 2. |

For a fixed positive definite commuting pair where $B_2<B_1$ is strict, continuity of finite-dimensional positive matrix powers makes the inequality persist under sufficiently small rotations. This is a conditional explanation of the mechanism; it does not assert strictness at every unequal commuting pair and is not a uniform kernel-checked result. The experiment supplies the six finite checks above. The proposed global characterization of when either bound is tighter remains open here.

The literature screen in #18947 read arXiv:2607.01805v1, Definitions 1–2, equations (6)–(9), (46)–(47), Theorems 1–2 and Section 4. Its recorded identifier/title/author searches with correction and counterexample found no settlement, and OpenAlex reported zero citing works; Semantic Scholar was rate-limited. The literature evidence is attributed to the preregistration producers; completeness is `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

Literature completeness and absence of subsequent corrections are `ASSUMED-UNVERIFIED`. The formal result is conditional on the literal source conventions in the statement echo. Continuity extensions, a full parameter classification and the source's other upper-bound claims are not independently formalized by this module.
