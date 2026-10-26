---
bibkey: shendemarkovbullock2004minimal
authors: Vivek V. Shende; Igor L. Markov; Stephen S. Bullock
year: 2004
title: Minimal Universal Two-Qubit CNOT-based Circuits
doi: 10.1103/PhysRevA.69.062321
url: https://arxiv.org/abs/quant-ph/0308033
claim: Almost every n-qubit unitary requires at least 4^n minus 1 one-parameter gates from a finite collection of one-parameter subgroups and constant gates.
strata_touched: []
license: citation-only
triage: anchor
---

# Parameter counting for exact circuit synthesis

In arXiv:quant-ph/0308033v3, §II, Lemma II.2 (PDF p. 2), a fixed
circuit topology with $m$ one-parameter placeholders defines a smooth map
from $\mathbb R^m$ to $SU(2^n)$. If $m<4^n-1$, Sard's theorem makes its
image measure zero. Accounting for the finitely many central phases and
the countably many finite topologies preserves the null-set conclusion.
The source separately derives a CNOT-count lower bound in Proposition
III.1; that bound is not a pulse-count result for the FIB menu.

The same standard dimensional mechanism applies to any compact Lie
target of real dimension $D$: countably many smooth word maps with fewer
than $D$ real parameters cover a null set. Fixed gates add discrete word
choices, not continuous dimensions. No bound on their number is needed
if their possible finite words form a countable set.

For periodic pulses and a finite-order fixed gate, bounded pulse count
can give finitely many templates with compact parameter tori. The
lower-dimensional-image claim can then also be seen by a covering
argument: a Lipschitz image of an $m$-dimensional compact domain is
covered by $O(\delta^{-m})$ target balls of volume $O(\delta^D)$, whose
total volume tends to zero for $m<D$. Smooth maps are Lipschitz here
with respect to fixed Riemannian metrics on compact domains.

The actual-menu substitution $d=F_{\ell+2}$ and target $PU(d)$ is in
[Static compatibility fibers, §61](../../docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md#61-fib-实际菜单的精确脉冲维数界).
It is a project-specific application of this established argument, not
a new general circuit lower-bound method. Exact generic synthesis is
different from fixed-error approximate synthesis and from the special
uniform circuit family needed for a decision problem. A generic target
may itself require a matrix description of exponential length in the
number of sites.
