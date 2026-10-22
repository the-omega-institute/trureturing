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

### Pell-index comparison

The following derivation is mathematical exposition, proved in prose. The kernel-checked settlement is the index-one case; the quantified Pell-index conclusion is not a Lean declaration in this delivery.

For $r\in\mathbb N$, define integer sequences by

$$p_0=3,\qquad n_0=1,\qquad
p_{r+1}=3p_r+8n_r,\qquad n_{r+1}=p_r+3n_r.$$

Induction shows that $p_r$ is odd and $p_r,n_r\ge1$. The Pell invariant is preserved because

$$p_{r+1}^2-8n_{r+1}^2
=(3p_r+8n_r)^2-8(p_r+3n_r)^2
=p_r^2-8n_r^2=1.$$

Both sequences strictly increase, since $p_{r+1}-p_r=2p_r+8n_r>0$ and $n_{r+1}-n_r=p_r+2n_r>0$. Eliminating $p_r$ gives

$$n_{r+2}=p_{r+1}+3n_{r+1}=6p_r+17n_r
=6n_{r+1}-n_r.$$

Define the integer $m_r$ and the asymptotic line value $x_r$ by

$$m_r=n_r+\frac{p_r+1}{2},\qquad x_r=\alpha n_r+\frac12,
\qquad \alpha=1+\sqrt2.$$

The positive Pell invariant implies $p_r>2n_r\sqrt2$, and rationalization gives the exact gap

$$0<m_r-x_r=\frac{p_r-2n_r\sqrt2}{2}
=\frac{1}{2(p_r+2n_r\sqrt2)}<\frac{1}{8n_r}.$$

The final inequality uses $p_r+2n_r\sqrt2>4n_r\sqrt2>4n_r$. Combining this gap with the sharp error bounds for the constructed tails gives

$$m_r-1<x_r<m_r<x_r+\frac{1}{8n_r}
<s_{n_r}<x_r+\frac{\alpha}{4n_r}<m_r+1.$$

Here $m_r-x_r<1$ gives the left endpoint, and $\alpha/(4n_r)<1$ gives the right endpoint because $n_r\ge1$ and $\alpha<4$. Thus

$$\lfloor s_{n_r}\rfloor=m_r,\qquad
\lfloor\alpha n_r+1/2\rfloor=m_r-1.$$

This proves the Pell-index floor comparison in prose for the constructed tails. Formalizing that quantified corollary remains open; this argument assumes neither uniqueness of positive tails nor their identification with finite truncations.

## Falsifier

A positive tail for $u=2$, $v=1$ satisfying the stated error bound and having $\lfloor s_1\rfloor=2$ would falsify the refutation. The formal result uses the exact index-one contradiction. Positive-tail uniqueness, ordinary finite-truncation identification and the quantified Pell-index family are outside the kernel-checked declaration.

## Evidence

- Kernel-checked settling: `D5.S1.Recurrence.ContinuedFractionTailBeattyRefutation.result : ¬ claim`.
- The axiom closure of every public declaration is contained in `{propext, Classical.choice, Quot.sound}`.
- The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
- The Scribe attaches one `OpenProblemResolutionClaim` with resolution `Refuted` to `result`.
- The source is documented by [the Library note](../Library/Asymptotics/fokkinkjoshi2025hiccup.md).

### Experiment

The pinned numerical check is in [the experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/cd9d66a5f5ff37b01ef63b93f24d14b8ca3278c3/docs/reports/fokkink-joshi-2025-continued-fraction-tail-beatty), from commit `cd9d66a5f5ff37b01ef63b93f24d14b8ca3278c3`; `check.py` has SHA-256 `4b86cbed203000b36f11ff68c34641aae75a3c1b172ee05d539477002567ee9b`. Command `python3 docs/reports/fokkink-joshi-2025-continued-fraction-tail-beatty/check.py` in that repository exits 0 with `RESULT PASS`. It checks $u=2,v=1$ through $1\le n\le1300$, the Theorem 24 control through $1\le n\le3000$, and the $v=-1$, $u\in\{1,2,3\}$ control through $1\le n\le3000$.

## Triage

| item | status | evidence and scope |
| --- | --- | --- |
| Pell family definition $(p_0,n_0)=(3,1)$, $p_{r+1}=3p_r+8n_r$, $n_{r+1}=p_r+3n_r$ | proved in prose | Recursive construction in the Pell-index comparison above; not a kernel-checked declaration. |
| Pell invariants, monotonicity and $n_{r+2}=6n_{r+1}-n_r$ | proved in prose | Induction, invariant expansion and elimination in the Pell-index comparison above. |
| Pell gap $0<m_r-(\alpha n_r+1/2)=1/(2(p_r+2n_r\sqrt2))<1/(8n_r)$ | proved in prose | Rationalization of the Pell invariant above, with $m_r=n_r+(p_r+1)/2$. |
| Pell-index floor comparison | proved in prose | The displayed comparison chain gives $\lfloor s_{n_r}\rfloor=m_r$ and $\lfloor\alpha n_r+1/2\rfloor=m_r-1$ for the constructed tails. |
| Lean formalization of the Pell-family corollary | open | No declaration states the quantified Pell-index comparison. |
| Numerical failures at indices $1,6,35,204,1189$ | computed | Pinned experiment above, exact tested scope $n\le1300$, exit 0, script SHA-256 above. |
| Theorem 24 control failures through $n\le3000$ | computed | Pinned experiment above, exact tested scope $n\le3000$, exit 0, script SHA-256 above; zero failures. |
| Original Conjecture 20 with $v=-1$, $u=1,2,3$ | computed | Pinned experiment above, exact tested scope $n\le3000$, exit 0, script SHA-256 above; no failures. |
| Failure mechanism: analytic positive $1/n$ correction crosses a Beatty integer at $n=1$ | proved | Kernel-checked by `result`, through `tail_exists`, `error_bounds`, `beta_value` and the floor contradiction. |
| Positive-tail uniqueness and identification with ordinary finite truncations | open | Not assumed by or encoded in `result`. |
| Equation (11) family | open | A neighbouring source question outside this claim. |
| Parameter pairs $(u,v)$ for which the generalized rounding assertion holds | open | The source's $u=1,v=\varphi-1$ case survives; no classification is asserted. |

### What the settlement shows

**Refuted by `result`:** the universal two-parameter rounding assertion after Equation (14), because a positive tail at $u=2$, $v=1$ satisfies the required $O(1/n)$ bound but fails the floor equality at $n=1$.

**Mechanism:** the fixed-point error is strictly positive and of order $1/n$, while the index-one Beatty line lies below the next integer. The Pell-index comparison above proves the extension in prose for the constructed tails. The kernel-checked settlement is the index-one case and does not identify all positive tails.

**Nearest statements that survive:** the source's Theorem 24 case $u=1$, $v=\varphi-1$ and the original Conjecture 20 specialization $v=-1$ are outside the refuted parameter choice. Their finite numerical controls are computed only over the scopes recorded above.

**Follow-up questions:** Lean formalization of the Pell-family corollary, positive-tail uniqueness, finite-truncation convergence, the Equation (11) family and the set of valid $(u,v)$ remain open.

## ASSUMED-UNVERIFIED

Literature completeness and priority remain `ASSUMED-UNVERIFIED`; the recorded source and citation screen is bounded. The Pell-family generalization, positive-tail uniqueness, finite-truncation convergence and all parameter classifications beyond the kernel-checked counterexample are not formalized here.
