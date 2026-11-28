---
slug: arias-noguerales-2026-riskca-complete-board-endpoint
bibkey: ariasnoguerales2026riskca
doi: 10.48550/arXiv.2611.34784
url: https://arxiv.org/abs/2611.34784v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/CellularAutomata/RiskCAEndpoint.paper_noninjective
---

# Noninjectivity on complete boards at the highest active RiskCA threshold

## Problem

Proposition 2 leaves injectivity open at the highest active threshold in the zero-growth deterministic local rule. [Proposition 2, p. 6](https://arxiv.org/pdf/2611.34784v1#page=6)

> if θ = Nmax − 1, attacks are possible only from saturated cells against cells with one unit, and injectivity is left open.

For every finite complete simple graph with vertex set $V$ of size at least two, capacity $M\ge3$, at least two available owner labels $P$, every fixed priority permutation, either fortification setting and every real $1<\rho<2$, is the synchronous deterministic local step noninjective when $g=0$ and $\theta=M-1$? Its carrier is the full product $(\{1,\ldots,P\}\times\{1,\ldots,M\})^V$. Configurations can be homogeneous or omit available labels. [Definition 2](https://arxiv.org/pdf/2611.34784v1#page=3) · [Registered scope](https://github.com/the-omega-institute/trureturing/issues/35259)

## Motivation

This is the complete-board branch of Proposition 2's residual case. The threshold $M-1$ forces a precise battle at every accepted attack. With zero growth, a configuration with common ownership is fixed. [Proposition 2, p. 6](https://arxiv.org/pdf/2611.34784v1#page=6) · [Proposition 4(a), p. 7](https://arxiv.org/pdf/2611.34784v1#page=7)

## Gap

The author's pinned Lean sources encode the rational rule and supply ingredients for the endpoint attack. Proposition 2 still records the endpoint as residual. The project proof uses the real battle rule and a finite-product carrier with pointwise equality. The connected incomplete-board branch with fortification disabled remains open in this formalization. [Author Lean sources](https://github.com/MaTeArNog/RiskAutomata/tree/67bb577bd35855cf605e4457ad8795ec0e923991/lean/RiskCA)

Both public theorems have an unfinished escape audit under CLAUDE.md §3.9. The four exact step observations depend on proof binders that the native source selector excludes from its parameter coordinates. The typed registration and its binding evidence remain open. [Escape audit](https://github.com/the-omega-institute/trureturing/issues/35259#issuecomment-7238336565)

## Route

Put $M$ units of owner $A$ at $u$, one unit of owner $B$ at a distinct $v$, and one unit of owner $A$ at all other vertices. The unique request goes from $u$ to $v$. It commits $M-1$ units and meets a defence of one. For $\rho\ge1$, the win is strict and $\lceil1/\rho\rceil=1$. The resulting $Y$ has owner $A$ everywhere, $M-2$ units at $v$ and one elsewhere. Zero growth fixes $Y$ and the two inputs differ at $u$. [Local rule](https://arxiv.org/pdf/2611.34784v1#page=4) · [Algorithm 1](https://arxiv.org/pdf/2611.34784v1#page=30)

## Falsifier

Any injective instance with the registered parameters would contradict the statement. Checking the two configurations requires legal counts, the actual priority and fortification rules, and both image equalities. With a single available owner the zero-growth map is the identity, which makes the two-owner hypothesis substantive.

## Evidence

The official pinned Mathlib backend checks `paper_collision_fixed_image` and `paper_noninjective` with only `propext`, `Classical.choice` and `Quot.sound`. The fixed-image theorem constructs and transports a collision on the indexed board. The noninjectivity theorem applies that result in the registered ratio band and composes the image equalities. The module has no D5 imports. The author's pinned MIT code supplies the indexed update and selected supporting proofs. [Source and license](https://github.com/MaTeArNog/RiskAutomata/tree/67bb577bd35855cf605e4457ad8795ec0e923991/lean/RiskCA) · [Literature and duplicate checks](https://github.com/the-omega-institute/trureturing/issues/35259)

## Triage

Admission uses `open-problem-resolution` for the registered complete-board statement with `utility: none`. The typed `Proved` resolution points to `paper_noninjective`. The proof shape of both theorems is `content` under the same-delivery inlining rule. The outer step of `paper_noninjective` specializes its live auxiliary `paper_collision_fixed_image` to the registered ratio band and composes the image equalities. Inlining that auxiliary and `indexed_collision` exposes the construction of the unique accepted attack and the exact decoded battle image.

### What the settlement shows

The registered noninjectivity statement is proved for $1<\rho<2$. The stronger fixed-image theorem holds for every real $\rho\ge1$ under the same board and configuration hypotheses. On complete boards a mixed resolved state has no interior cells and a homogeneous one has no positive threat, so fortification sends nothing in either case. The collision resolves the complete-board branch of Proposition 2.

## ASSUMED-UNVERIFIED

The literature check is bounded to the sources and indexes recorded in the preregistration. A formal extension to connected incomplete boards with fortification disabled remains open. [Search scope](https://github.com/the-omega-institute/trureturing/issues/35259)
