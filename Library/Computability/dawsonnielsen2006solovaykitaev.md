---
bibkey: dawsonnielsen2006solovaykitaev
authors: Christopher M. Dawson; Michael A. Nielsen
year: 2006
title: The Solovay-Kitaev algorithm
doi: null
url: https://arxiv.org/abs/quant-ph/0505030
claim: At fixed local dimension a finite inverse-closed dense instruction set admits polylogarithmic-length approximation of target unitaries.
strata_touched: []
license: citation-only
triage: anchor
---

# Local compilation and the length of a task trajectory

The author version arXiv:quant-ph/0505030v2, Definition 1 (PDF p. 2),
requires a finite inverse-closed instruction set in $SU(d)$ that generates
a dense subgroup. Theorem 1 (PDF p. 4) supplies approximation in operator
norm with length $O(\log^c(1/\delta))$. Its algorithmic discussion on the
same page distinguishes compressed output from actually listing the
gate sequence. The explicit-output time is also polylogarithmic. Section
5 extends the construction to $SU(d)$; dimension-dependent constants
must not be treated as uniform when the entire register dimension grows.
Effective target descriptions, required numerical arithmetic and the
initial finite net are part of an effective compiler's hypotheses.

For $L\ge1$ target unitaries and unitary approximants, telescoping gives

$$
\left\|\widetilde U_L\cdots\widetilde U_1-U_L\cdots U_1\right\|
\le\sum_{i=1}^L\|\widetilde U_i-U_i\|.
$$

Indeed, replace one factor at a time; left and right multiplication by
the remaining unitary factors preserves the norm. Taking each error
at most $\epsilon/L$ gives total error at most $\epsilon$. For fixed
local dimension, targets in that fixed $SU(d)$ contract and a fixed
instruction set, this yields total compiled
length $O(L\log^c(L/\epsilon))$ for $0<\epsilon<1/2$. Targets, sites,
wiring, preparation, compilation and readout must themselves be acquired
and charged. The estimate does not supply a polynomial bound on $L$.
It concerns unitary implementation error, not an arbitrary physical
noise process or an automatic constant probability of solving a task.

Adriano Barenco's *A Universal Two-Bit Gate for Quantum Computation*,
[arXiv:quant-ph/9505016v1](https://arxiv.org/abs/quant-ph/9505016v1),
defines adequacy on PDF p. 1 using arbitrary-precision networks of copies
of a gate; the construction occupies pp. 2–4. A gate type can be placed
on different wires. Repeated powers of one fixed matrix on the same
register commute, as do all elements of their closure, so that restricted
operation set cannot generate a noncommutative unitary group. Finite
words over a finite discrete menu are countable and do not exactly
enumerate a continuous unitary group. The continuously parameterized
FIB menu of Assumption 55.2 is a different resource contract.
