---
slug: fokkink-joshi-2025-continued-fraction-tail-beatty
bibkey: fokkinkjoshi2025hiccup
doi: 10.1007/s11139-025-01305-1
url: https://arxiv.org/abs/2507.16956v4
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/ContinuedFractionTailBeattyRefutation.result
---

# Continued-fraction tails with u = 2 and v = 1 miss the Beatty sequence

## Problem

R. Fokkink and G. Joshi, *On Cloitre's hiccup sequences*, arXiv:2507.16956v4, Section 4 after Equation (14), state the two-parameter family

$$s_n=nu+v+\frac{n^2}{s_{n+1}}$$

and its asymptotic line

$$\alpha=\frac{u+\sqrt{u^2+4}}2,\qquad
\beta=\frac{v\alpha^2-\alpha}{\alpha^2+1}.$$

They state that positive tails satisfying $s_n=\alpha n+\beta+O(1/n)$ round down to the Beatty sequence with slope $\alpha$ and offset $\beta$. The settling declaration is `D5.S1.Recurrence.ContinuedFractionTailBeattyRefutation.result`.

### Statement echo

The Lean `beta`, `IsTail` and `claim` definitions retain the source's radical slope, offset, positive-tail recurrence, uniform $C/n$ error bound, and floor equality. The `claim` body is displayed in the Scribe and the `result` proves its negation.

## Motivation

The source's generalization would transfer an asymptotic estimate into an exact floor identity. The settlement supplies a positive-tail counterexample at $u=2$, $v=1$.

## Gap

The preregistration is [issue #18586](https://github.com/the-omega-institute/trureturing/issues/18586). The source's Section 4 statement and Theorem 24 were read. The recorded literature screen found no settlement of this generalization in its searched scope; completeness remains `ASSUMED-UNVERIFIED`.

## Route

Set $\alpha=1+\sqrt2$ and $\beta=1/2$. On the closed set of bounded real sequences with $0\le e_k\le1/(k+1)$, the error operator induced by the recurrence preserves the set and is a contraction with factor $1/4$. Its fixed point gives positive tails with

$$\frac1{8n}<s_n-(\alpha n+1/2)<\frac{\alpha}{4n}.$$

At $n=1$, the Beatty line has floor $2$, while the recurrence gives $s_1=3+1/s_2>3$. Therefore the universal rounding assertion is false. The module uses the existing frozen `metallicValue` owner for the metallic mean while keeping the source radical literal in `claim`.

## Falsifier

A positive tail for $u=2$, $v=1$ satisfying the stated error bound and having $\lfloor s_1\rfloor=2$ would falsify the refutation. The formal result uses the exact index-one contradiction. Positive-tail uniqueness, ordinary finite-truncation identification and the quantified Pell-index family are outside the kernel-checked declaration.

## Evidence

- Kernel-checked settling: `D5.S1.Recurrence.ContinuedFractionTailBeattyRefutation.result : ¬ claim`.
- The axiom closure of every public declaration is contained in `{propext, Classical.choice, Quot.sound}`.
- The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
- The Scribe attaches one `OpenProblemResolutionClaim` with resolution `Refuted` to `result`.
- The source is documented by [the Library note](../Library/Asymptotics/fokkinkjoshi2025hiccup.md).

### Experiment

The pinned numerical check is [`check.py`](https://github.com/the-omega-institute/trureturing-experiments/tree/cd9d66a5f5ff37b01ef63b93f24d14b8ca3278c3/docs/reports/fokkink-joshi-2025-continued-fraction-tail-beatty/check.py), from commit `cd9d66a5f5ff37b01ef63b93f24d14b8ca3278c3`; its SHA-256 is `4b86cbed203000b36f11ff68c34641aae75a3c1b172ee05d539477002567ee9b`. Command `python3 docs/reports/fokkink-joshi-2025-continued-fraction-tail-beatty/check.py` exits 0 with `RESULT PASS`. It checks $u=2,v=1$ through $n\le1300$, the Theorem 24 control through $n\le3000$, and the $v=-1$, $u\in\{1,2,3\}$ control through $n\le3000$.

## Triage

| item | status | evidence and scope |
| --- | --- | --- |
| Pell family definition $(p_0,n_0)=(3,1)$ with the stated recurrences | open | The supplied derivation was checked against the route, but no declaration encodes it. |
| Pell invariants, monotonicity and $n_{r+2}=6n_{r+1}-n_r$ | open | Mathematical derivation only; no kernel-checked declaration in this delivery. |
| Pell gap $0<m_r-(\alpha n_r+1/2)<1/(8n_r)$ | open | The supplied derivation is outside the module's formal statement. |
| Pell-index floor comparison | open | It would follow from the sharp tail bounds plus the Pell gap, but the quantified conclusion is not declared. |
| Numerical failures at indices $1,6,35,204,1189$ | computed | Pinned experiment above, exact tested scope $n\le1300$, exit 0, script SHA-256 above. |
| Theorem 24 control failures through $n\le3000$ | computed | Pinned experiment above, exact tested scope $n\le3000$, exit 0, script SHA-256 above; zero failures. |
| Original Conjecture 20 with $v=-1$, $u=1,2,3$ | computed | Pinned experiment above, exact tested scope $n\le3000$, exit 0, script SHA-256 above; no failures. |
| Failure mechanism: analytic positive $1/n$ correction crosses a Beatty integer at $n=1$ | proved | Kernel-checked by `result`, through `tail_exists`, `error_bounds`, `beta_value` and the floor contradiction. |
| Positive-tail uniqueness and identification with ordinary finite truncations | open | Not assumed by or encoded in `result`. |
| Equation (11) family | open | A neighbouring source question outside this claim. |
| Parameter pairs $(u,v)$ for which the generalized rounding assertion holds | open | The source's $u=1,v=\varphi-1$ case survives; no classification is asserted. |

### What the settlement shows

**Refuted by `result`:** the universal two-parameter rounding assertion after Equation (14), because a positive tail at $u=2$, $v=1$ satisfies the required $O(1/n)$ bound but fails the floor equality at $n=1$.

**Mechanism:** the fixed-point error is strictly positive and of order $1/n$, while the index-one Beatty line lies below the next integer. This settles the named generalization without identifying all positive tails or proving the Pell-index extension.

**Nearest statements that survive:** the source's Theorem 24 case $u=1$, $v=\varphi-1$ and the original Conjecture 20 specialization $v=-1$ are outside the refuted parameter choice. Their finite numerical controls are computed only over the scopes recorded above.

**Follow-up questions:** the Pell-family corollary, positive-tail uniqueness, finite-truncation convergence, the Equation (11) family and the set of valid $(u,v)$ remain open.

## ASSUMED-UNVERIFIED

Literature completeness and priority remain `ASSUMED-UNVERIFIED`; the recorded source and citation screen is bounded. The Pell-family generalization, positive-tail uniqueness, finite-truncation convergence and all parameter classifications beyond the kernel-checked counterexample are not formalized here.
