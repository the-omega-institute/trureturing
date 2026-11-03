---
slug: shchukin-van-loock-2016-higher-order-epr-tightness
bibkey: shchukinvanloock2016higherorderepr
doi: 10.1103/PhysRevA.93.032114
url: https://arxiv.org/abs/1511.08444v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/FockSpace/HigherOrderEPRTightness.result
---

# The zero higher-order EPR bound is tight at every positive order

## Problem

E. Shchukin and P. van Loock, *Higher-order EPR correlations and inseparability conditions for continuous variables*, arXiv:1511.08444v1 (Phys. Rev. A 93, 032114, 2016), subsection “Approach two”, state the following conjecture in `bip-ent2.tex`, lines 961–963:

> Our conjecture is that the inequality \eqref{eq:nS:1} cannot be violated by Gaussian states (including all inseparable ones) and the inequality \eqref{eq:nS:2} is tight. We verified this by numerical computations, but we could not find rigorous proofs.

Here the source's inequalities (nS:1) and (nS:2), at lines 914–924, concern two bosonic modes and every positive integer $n$:

$$
\left\langle(\hat a^{\dagger n}\pm\hat b^n)(\hat a^n\pm\hat b^{\dagger n})\right\rangle
\ge
\begin{cases}
n! & \text{for separable states},\\
0 & \text{for all states}.
\end{cases}
$$

Issue [#24246](https://github.com/the-omega-institute/trureturing/issues/24246) fixes the reading to the tightness clause: for every $n\ge1$, either sign $\sigma\in\{1,-1\}$ and every $\varepsilon>0$, there is a normalized finitely supported occupation-basis vector $\psi$ with $\|(\hat a^n+\sigma\hat b^{\dagger n})\psi\|^2<\varepsilon$. This is proved. The Gaussian clause is a separate question.

The source and its bibliographic locator are recorded in [the literature note](../Library/Observer/shchukinvanloock2016higherorderepr.md).

## Motivation

The gap between the separable threshold $n!$ and the all-state lower bound $0$ measures the possible violation of this higher-order inseparability criterion. Tightness asks whether arbitrarily small values are available at each order, rather than merely values below the separable threshold. Finite occupation-basis witnesses keep every operator product in the expression defined.

## Gap

Issue #24246 records the bounded literature check:

- The arXiv source contains the conjecture; the issue reports that arXiv lists only v1.
- Web searches for Shchukin, van Loock, higher-order EPR, tight bound and conjecture found related moment-criterion literature but no proof of the tightness clause.
- The search seat reported five citing works listed through OpenAlex and OpenCitations, with no settlement; those readings were not independently reproduced.
- The preregistration's repository search found no existing record or D5 theorem giving this settlement.

`not-found-in-searched-scope`.

## Route

Write $H_0=0$ and $H_m=\sum_{j=1}^m1/j$. For natural $n\ge1$ and $m\ge1$, and a complex $\sigma$, the private definitions `taper`, `coefficient` and `vector` give

$$
f_k=1-\frac{H_k}{H_m},\qquad
c_k=\sqrt{\frac{(nk)!}{(nk+n-1)!}},\qquad
v=\sum_{k=0}^{m}(-\sigma)^k f_kc_k\,|nk+n-1,nk\rangle.
$$

1. **Matching the operator images.** For natural $n\ge1$ and every natural $k$, `lower_chain` and `upper_chain` show that annihilation of $c_{k+1}|n(k+1)+n-1,n(k+1)\rangle$ and creation of $c_k|nk+n-1,nk\rangle$ both give $\sqrt{n(k+1)}|n(k+1)-1,n(k+1)\rangle$. For $n\ge1$, $m\ge1$ and arbitrary complex $\sigma$, `taper_image` consequently identifies the signed output as
   $$
   \sum_{k=0}^{m-1}(-\sigma)^{k+1}\sqrt{n(k+1)}(f_{k+1}-f_k)\,|n(k+1)-1,n(k+1)\rangle.
   $$
   The first annihilation term vanishes because its first occupation is $n-1$; the last creation term vanishes because $f_m=0$.
2. **The Dirichlet sum.** For every natural $n$ and natural $m\ge1$, `dirichlet_energy` proves
   $$
   \sum_{k=0}^{m-1}\left(\sqrt{n(k+1)}(f_{k+1}-f_k)\right)^2=\frac{n}{H_m},
   $$
   using $f_{k+1}-f_k=-1/((k+1)H_m)$. For $n\ge1$, $m\ge1$ and $\sigma=1$ or $\sigma=-1$, `taper_energy` gives $\operatorname{normSq}(\operatorname{annihilateA}\,n\,v+\sigma\,\operatorname{createB}\,n\,v)=n/H_m$: the output sites are distinct and the phase factors have modulus one.
3. **A positive normalization denominator.** For natural $n\ge1$, every natural $m$ and every complex $\sigma$, `taper_norm_bound` proves $Z=\operatorname{normSq}(v)\ge1/(n-1)!>0$ from the initial coefficient. For every natural $n$, complex $\sigma$ and finitely supported $v$ with $\operatorname{normSq}(v)>0$, `normalize` supplies a unit vector whose output squared norm is the original output squared norm divided by $\operatorname{normSq}(v)$.
4. **Arbitrarily small values.** For every real $b$, `harmonic_large` supplies a natural $m\ge1$ with $H_m>b$. With $n\ge1$, $\sigma\in\{1,-1\}$ and $\varepsilon>0$, the proof of `result` chooses $b=n!/\varepsilon$, normalizes $v$, and obtains
   $$
   \frac{n}{H_mZ}\le\frac{n!}{H_m}<\varepsilon.
   $$

## Falsifier

A settlement would miss the source's question if the formal operators or normalization differed from the occupation-basis ones. The module defines:

- `normSq` as $\sum_{r,s}|\psi(r,s)|^2$ for a finitely supported complex function on $\mathbb N\times\mathbb N$;
- `annihilateA n` by $|r,s\rangle\mapsto\sqrt{r!/(r-n)!}\,|r-n,s\rangle$ when $n\le r$, and zero otherwise;
- `createB n` by $|r,s\rangle\mapsto\sqrt{(s+n)!/s!}\,|r,s+n\rangle$;
- `claim` with the quantifiers over every natural $n\ge1$, both complex signs and every positive real tolerance, and with exact unit normalization.

On the usual embedding of finite occupation-basis vectors into two-mode Fock space, these basis actions are $\hat a^n$ and $\hat b^{\dagger n}$. Their adjoints on this common finite domain identify the source's expectation with the squared norm of the signed output. This Hilbert-space interpretation is not itself formalized in the module. The witnesses require no assertion about an infinite-support operator domain, a Gaussian class or a mixed-state representation.

## Evidence

The canonical source is `D5/S3/Quantum/FockSpace/HigherOrderEPRTightness.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/FockSpace/HigherOrderEPRTightness.lean.json`.

Declaration statements:

- `result`: `sha256:b446ab088c1fef6760304a9919643979e6fa25e3b3985be5bf9a2e21baecfe48`;
- `claim`: `sha256:a43ae021a34038e2f362856594a92458d4f05049b6cc750d123d8b263654f3d2`.

## Triage

Tier 1 conjecture in a 2015 preprint associated with a 2016 journal article, preregistered in issue #24246 before any Lean. Its presence in the journal text is `ASSUMED-UNVERIFIED`.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $n\ge1$, every complex $\sigma$ equal to $1$ or $-1$, and every real $\varepsilon>0$, there exists a finitely supported $\psi:\mathbb N\times\mathbb N\to\mathbb C$ with `normSq` equal to $1$ and `normSq` of $\operatorname{annihilateA}\,n\,\psi+\sigma\,\operatorname{createB}\,n\,\psi$ strictly below $\varepsilon$.

**Computed, not formalized:** none.

**Argued, not formalized.**

- *Why the taper works.* For fixed natural $n\ge1$ and $m\ge1$, any real taper $g_0=1$, $g_m=0$ satisfies
  $$
  1=\left(\sum_{j=1}^{m}(g_j-g_{j-1})\right)^2
  \le\left(\sum_{j=1}^{m}nj(g_j-g_{j-1})^2\right)\left(\sum_{j=1}^{m}\frac1{nj}\right).
  $$
  Cauchy–Schwarz therefore bounds this Dirichlet sum below by $n/H_m$, with equality for increments $-1/(jH_m)$. The harmonic taper minimizes this unnormalized sum with these endpoints. This does not establish optimality of the normalized quotient or of a fixed support cutoff over all states.
- *Sharpness as an infimum.* For fixed $n\ge1$ and either sign, the set of finite unit-state energies is nonempty by `result` with $\varepsilon=1$, and is bounded below by $0$ because `normSq` is a sum of squares. Any proposed positive lower bound $d$ is contradicted by `result` with $\varepsilon=d$. Thus its real infimum is $0$; no separate infimum declaration is proved. Under the Fock-space identification above, the same conclusion extends to any larger admissible state class containing these witnesses whose expectation is nonnegative.
- *Finite-support strictness.* For $n\ge1$, $\sigma\in\{1,-1\}$ and a nonzero finite vector, choose a nonzero amplitude with maximal second occupation $s$. Creation contributes a nonzero amplitude at second occupation $s+n$; its basis map is injective, and annihilation cannot contribute there because it leaves the second occupation unchanged. Thus no such finite vector has zero output. Strictness for broader infinite-support domains is not settled here.
- *Unit phases.* If $|\sigma|=1$, the same finite formula for $v$ has phase factors of modulus one; its operator cancellation and squared-norm sums are unchanged, so the normalized error is again at most $n!/H_m$. This extends the argument to unit complex phases, but `result` quantifies only over the two signs.
- *Effect on the source.* For each fixed $n\ge1$ and each real $R>1$, take $\varepsilon=n!/R$ in `result`; under the occupation-basis identification and the source's separable bound, this supplies a violation by more than $R$. The source's factor-four examples at lines 925–958 therefore do not exhaust the attainable violation. The tightness clause is supplied without changing the source's $n=2$ tightness theorem. The separate Gaussian-exclusion clause, and hence the all-order Gaussian exclusion sought in the source's hierarchy discussion, receives no proof from this settlement; neither separability nor Gaussianity is defined in the module.

## ASSUMED-UNVERIFIED

The bounded literature search in issue #24246 does not establish exhaustive worldwide novelty or priority. Its web-search results and its report that arXiv lists only v1 were not independently reproduced. The five citing-work readings reported by the search seat were not reproduced: Barral et al., arXiv:2301.03909; Zhang et al., Phys. Rev. Lett. 127, 150502; Zhang et al., Phys. Rev. Lett. 130, 093602; Citeli de Freitas et al., Entropy 22, 980; and Dodonov, Quantum Rep. 7, 34. The APS text was not read, so the conjecture's presence there and the published equation numbering remain unverified; the quotation is from arXiv v1.

Everything in “Argued, not formalized”, including the infimum interpretation, finite-support nonattainment, phase extension, optimization of the Dirichlet sum and consequences using the source's separable bound, lies outside the statement of `result`. The embedding into completed Fock space, adjoint and domain identities, mixed states, strictness on infinite-support domains, Gaussian claims, and the source's other inequalities are not formalized here.
