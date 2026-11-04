---
slug: consiglio-apollaro-wiesniak-2022-xmems-css-shape
bibkey: consiglioapollarowiesniak2022separability
doi: 10.1103/PhysRevA.106.062413
url: https://arxiv.org/abs/2209.01430v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation.result
---

# A closest fully separable state of an X-MEMS need not have the conjectured shape

## Problem

M. Consiglio, T. J. G. Apollaro and M. Wieśniak, *A Variational Approach to the Quantum Separability Problem*, arXiv:2209.01430v2 (Phys. Rev. A 106, 062413, 2022), Appendix A, subsection “$n$-qubit $X$-MEMS”, state in `PRA_v2.tex`, line 459 (acronym macros expanded):

> While we have not explicitly derived the CSS of $n$-qubit X-MEMS in general, we conjecture that it is of the form

The following matrix is Eq. (A11), lines 460–473. Put $N=2^{n-1}$ and order computational basis words with qubit 1 most significant. Its diagonal entries are $a/2$ at the all-zero and all-one words, $b/(N-1)$ at every other first-bit-zero word, and $(1-a-b)/(N-1)$ at every other first-bit-one word. Its opposite corners are $d,d^*$ and all other entries vanish. Line 474 restricts $a,b\in[0,1]$, $a+b\le1$, and $|d|\le a/2$.

The source defines the CSS as a minimizer over fully separable states of $D_{HS}(\rho,\sigma)=\operatorname{Tr}((\rho-\sigma)^2)$ (Section II, lines 70–93). The definitions and source locator are in [the literature note](../Library/Divergence/consiglioapollarowiesniak2022separability.md).

Issue [#25134](https://github.com/the-omega-institute/trureturing/issues/25134) fixes the low-branch reading: for every integer $n\ge2$ and every $\gamma\in\mathbb C$ with $|\gamma|\le1/(N+1)$, there exists a fully separable $\sigma$ of Eq. (A11) such that

$\operatorname{hsSq}(\rho,\sigma)\le\operatorname{hsSq}(\rho,\tau)$ for every fully separable $\tau$.

Here $\rho=\operatorname{xmems}(n,\gamma)$ has diagonal $1/(N+1)$ at all first-bit-zero words and the all-one word, zero at the remaining words, and opposite corners $\gamma,\gamma^*$; this is Eq. (A1) on the branch where $f=g=1/(N+1)$ (lines 341–373). The module defines $\operatorname{hsSq}(\rho,\sigma)=\operatorname{Re}\operatorname{Tr}((\rho-\sigma)^\dagger(\rho-\sigma))$. The statement asserts attainment as well as comparison with every fully separable competitor. It is refuted.

## Motivation

The proposed shape reduces an optimization over all fully separable multiqubit states to parameters $a,b,d$. Consiglio, Apollaro and Wieśniak (2022, arXiv:2209.01430v2) use this reduction for their three-qubit calculation and their proposed general X-MEMS entanglement curves. Its validity determines whether optimization within that family gives the fully separable distance of the original state.

## Gap

Issue #25134 records the bounded literature check before any Lean:

- The arXiv v2 source states the conjecture. The orchestrator (Claude Code, Opus) also reports reading its restatement in M. Consiglio, *Variational Quantum Algorithms for Many-Body Systems* (2025), arXiv:2502.11985v1, Appendix 10.C.
- OpenAlex returned 16 citing works; the search contributor screened the 13 with arXiv versions and reported no settlement.
- The orchestrator reports searches for closest separable states of X-MEMS and multiqubit X-states, Zenodo searches, and repository searches without a settlement.

`not-found-in-searched-scope`.

## Route

All indices in the following three-qubit calculation run from $0$ to $7$ in binary order. Put $\rho=\operatorname{xmems}(3,11/112)$.

1. **A necessary separability inequality.** For a product $P=p_1\otimes p_2\otimes p_3$ in which every $p_k$ is positive semidefinite with trace one, `product_bounds` bounds $\operatorname{Re}P_{07}$ both by $P_{11}/6+3P_{66}/2$ and by $P_{00}/12+P_{33}/12+3P_{55}/4+3P_{66}/4$; diagonal entries here are real. For every fully separable three-qubit matrix $\sigma$, `separable_bounds` proves the convex combination of these inequalities with weights $1/5$ and $4/5$. The lemma `fullySeparable_iff`, for every $n$ and every matrix on $n$ binary coordinates, identifies the real convex hull of products of one-qubit density matrices with `IsFullySeparableLocal`.
2. **A bound over the entire proposed family.** For arbitrary real $a,b$ and complex $d$, `shape_distance` expands the squared distance from $\rho$ to `cssShape 3 a b d`. When the matrix is fully separable and satisfies `IsCssShape`, `shape_lower` proves $109/23520\le\operatorname{hsSq}(\rho,\sigma)$. In the expansion, put $s=a/2$, $B=b/3$ and $C=(1-a-b)/3$; the preceding necessary inequality becomes $\operatorname{Re}d\le s/15+B/10+3C/2$, and completing squares gives the lower bound.
3. **A closer fully separable competitor.** For $0\le u\le1$ and $c\in\mathbb Z/3\mathbb Z$, `localState_density` proves that the projector onto $\sqrt u|0\rangle+\chi(c)\sqrt{1-u}|1\rangle$ is a density matrix, where $\chi$ is the standard additive character. The fixed `phaseProduct` uses local parameters $(9/10,a)$, $(199/400,b)$ and $(199/400,-a-b)$. With $a,b\in\mathbb Z/3\mathbb Z$, `tau_mixture` expresses the fixed matrix `tau` as $5/54$ times the sum of these nine product densities plus $1/6$ times $|111\rangle\langle111|$. For every pair of three-bit words, `phase_average_entry` proves that this character average removes every off-diagonal entry except the opposite corners. The lemma `tau_separable` proves `IsFullySeparableLocal tau` without additional hypotheses.
4. **Strict comparison.** The lemmas `tau_distance` and `distance_gap`, without additional hypotheses, give $\operatorname{hsSq}(\rho,\operatorname{tau})=417965512477/90316800000000<109/23520$. Applying `claim` at $n=3$, $\gamma=11/112$, whose norm is at most $1/5$, contradicts `shape_lower` and this comparison. This proves `result : ¬ claim`.

## Falsifier

The refutation would not answer the source conjecture if the matrix shape, feasible set or distance differed from the source's. The module's `cssShape` and `IsCssShape` retain all parameters and restrictions of Eq. (A11); full separability is a separate requirement. Its `xmems` uses only the low branch, so the conclusion does not depend on an interpretation of the printed high branch. Its trace formula agrees with the source's squared distance for Hermitian density matrices; `hsSq_entries` proves its entrywise squared-modulus expression for arbitrary matrices on $n$ binary coordinates, without a Hermitian hypothesis.

`IsFullySeparableLocal` means a finite mixture of products of one-qubit density states, with nonnegative real weights summing to one. This is the source's fully separable feasible set: each local density matrix has a finite spectral decomposition into pure one-qubit projectors; expanding the tensor product gives pure product projectors with nonnegative weights summing to one. Conversely, each pure product is a product of local density matrices. This identification does not replace full separability by positivity of partial transposes. No infimum or supremum is used in `claim` or `result`.

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:d31914d1263dcfe111656c06b4b86e1aac0f6c0a9903509b4e79973242b28039`;
- `claim`: `sha256:3e7507865732992c05d06712c63bee86e7a2fed3c79e55c89f80c3a512a842c1`.

## Triage

Tier 1 conjecture of a 2022 paper, preregistered in issue #25134 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that for every integer $n\ge2$ and every complex $\gamma$ with $|\gamma|\le1/(2^{n-1}+1)$ there exists a fully separable matrix of the restricted shape `IsCssShape` whose squared Hilbert–Schmidt distance to `xmems n γ` is at most that of every fully separable matrix.

**Computed, not formalized:** None.

**Argued, not formalized.**

- *Mechanism and missing structure.* Exchange of qubits 2 and 3 only identifies words in the same permutation orbit; it does not equate every population within a first-bit class or equate the two endpoints. The closer competitor preserves this exchange symmetry while escaping the additional equalities of Eq. (A11). Thus the obstruction concerns the population restrictions, even within matrices supported only on the diagonal and opposite corners.
- *Why target symmetry needs a feasible-set hypothesis.* At the real registered target, the unitary swapping only $|000\rangle$ and $|111\rangle$ fixes the target, but sends the product $|00\rangle\otimes(|0\rangle+|1\rangle)/\sqrt2$ to $(|001\rangle+|111\rangle)/\sqrt2$. The latter has Schmidt rank two across the first qubit versus the other two, so this unitary does not preserve full separability. Target invariance alone therefore supplies no averaging argument for equal endpoint populations.
- *A weaker symmetry reduction survives.* For $n\ge2$ and $|\gamma|\le1/(2^{n-1}+1)$, permutations of qubits $2,\ldots,n$ preserve full separability and fix the target. Averaging a fully separable competitor over these permutations remains fully separable, and convexity of the squared norm, together with unitary invariance, bounds its distance by the original distance. Hence, if a closest state exists, such averaging gives a permutation-invariant closest state. Whether an enlarged X-state family describes all required minima is open here.
- *Effect on the paper.* The source's three-qubit matrix (A8) is the $n=3$ case of (A11). At the registered instance, the lemmas `shape_lower`, `tau_separable`, `tau_distance` and `distance_gap` exclude every fully separable matrix of (A8) as a global minimizer. Consequently the restricted-shape derivation does not certify the three-qubit CSS calculation or its generalization underlying the claimed analytical entanglement curves in the three-qubit plot (`PRA_v2.tex`, line 275) and the two-to-nine-qubit plot (line 493). The quartic-parameter prescription and the infinite-qubit limit require independent justification beyond that derivation; this refutation supplies neither their replacement nor a pointwise assessment of all plotted values. It does not decide the separate conjecture about bound entanglement of the PPT-optimized (A8) state. The two-qubit calculation, the algorithm's performance, and the comparisons with concurrence are not settled by `result`.

## ASSUMED-UNVERIFIED

The literature check is bounded and does not establish exhaustive worldwide novelty or priority. The source text read is arXiv:2209.01430v2, member `PRA_v2.tex`, md5 `611cfcad16eb65b213bb7ddff8372815`; the published journal text was not read, so preservation of the conjecture there is unverified. The thesis reading, OpenAlex count, citing-work screening and external searches are attributed reports in #25134 and were not independently reproduced. The reported four-qubit obstruction in that issue was not reproduced and is not part of this settlement.

The computations and arguments in “What the settlement shows”, including the symmetry reduction and the consequences for the source's derivations, are not additional formal statements of `result`. The pure-product versus mixed-product spectral-decomposition bridge is an explanatory argument here. The actual CSS and its entanglement value, the high branch, a general range of counterexamples, and any corrected full-family characterization remain undetermined by this module. The source's optimization code, numerical plots and claimed asymptotic formula were not independently reproduced.
