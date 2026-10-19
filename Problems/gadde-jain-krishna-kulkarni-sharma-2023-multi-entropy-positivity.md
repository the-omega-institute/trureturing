---
slug: gadde-jain-krishna-kulkarni-sharma-2023-multi-entropy-positivity
bibkey: gaddejainkrishnakulkarnisharma2024multientropy
doi: 10.1007/JHEP02(2024)025
url: https://arxiv.org/abs/2308.16247v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/MultiEntropyPositivityRefutation.result
---

# Positivity of the multi-entropy replica invariant

## Problem

A. Gadde, S. Jain, V. Krishna, H. Kulkarni and T. Sharma, *Monotonicity conjecture for multi-party entanglement. Part I*, JHEP 02 (2024) 025, arXiv:2308.16247v1, Section 7:

> “Although we found that E_n is positive in the examples we studied, it would be nice to prove this in general and to see if there is any relation between the positivity of E_n and the coarse-graining monotonicity.”

Footnote 2 makes positivity the assumption needed for the logarithm in Eq. (1.11). The [literature note](../Library/QuantumChannels/gaddejainkrishnakulkarnisharma2024multientropy.md) gives the full quotation and the replica convention in Eqs. (1.10)–(1.11). Issue [#17540](https://github.com/the-omega-institute/trureturing/issues/17540) fixes the finite-dimensional statement with all quantifiers before formalization.

The question is refuted. For the normalized totally antisymmetric three-qutrit state
$\psi_{ijk}=\varepsilon_{ijk}/\sqrt{6}$,

$$E_4^{(3)}(\psi)=\frac{-1680}{6^{16}}=\frac{-35}{58773123072}<0.$$

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $n^{q-1}$ replicas on $(\mathbb Z/n)^{q-1}$ | `E`, replica index `Fin (q - 1) → ZMod n` | Literal contraction in Eq. (1.10). |
| Independent translations for the first $q-1$ parties; last party fixed | `StabilizerMultiEntropyCollapse.shift` | The source labels parties from one; Lean labels from zero. |
| Arbitrary finite local bases and complex pure-state amplitudes | `E`, dependent family `L`, its `Fintype` instances and amplitude `ψ` | No dimension restriction in `claim`. |
| Normalization | `IsUnitState` | Sum of `Complex.normSq` is one, exactly the convention in #17540. The proof uses the existing `unitVector` predicate through the private consumed correspondence `unit_norm_iff`. |
| Every $n,q\ge2$ has positive real invariant | `claim` | Positive real part and zero imaginary part; `NeZero n` is implied by $n\ge2$ and supports `ZMod n`. |
| Negative answer at $n=4,q=3$ | `result : ¬ claim` | One normalized instance disproves the universal assertion. |

## Motivation

The Rényi multi-entropy in Eq. (1.11) uses a real logarithm of $E_n^{(q)}$. Positivity of the contraction is therefore a separate mathematical requirement from coarse-graining inequalities formulated directly for $E$. A negative normalized pure-state instance tests that requirement without assuming a holographic, Gaussian or stabilizer description.

## Gap

The source explicitly leaves general positivity unproved. The bounded literature readings recorded in #17540 cover the source, Gadde–Jain arXiv:2406.17447 and 2509.06348, arXiv:2411.00935 and 2602.16770, Penington–Walter–Witteveen arXiv:2211.16045, and Gadde–Krishna–Sharma arXiv:2206.09723 and 2304.06082. The additional eight screened works are arXiv:2410.08284, 2504.16589, 2606.04470, 2606.18361, 2510.18408, 2511.00905, 2509.00593 and 2401.04236. The preregistration also records search-seat screens of Grassl–Rötteler–Beth, Christandl–Schuch–Winter and Ellis-Monaghan–Moffatt, and the orchestrator's QIQC catalog screen. These readings contain no negative value of this replica invariant. Negative genuine multi-entropies and negative coefficients in a plethystic logarithm are different statements.

Literature status: `not-found-in-searched-scope`; completeness is `ASSUMED-UNVERIFIED`. Reflection-positive subclasses do not establish positivity of every replica torus.

## Route

The determinant of the three selected rows of the identity matrix gives $\varepsilon$. Its six nonzero values have square one, so division by $\sqrt6$ normalizes the state. Tracing the unshifted third party gives the two-qutrit marginal

$$\rho_{AB}=\frac{I-F}{6},$$

where $F$ exchanges the two qutrits. Reindexing the replica grid yields the periodic contraction

$$E_4^{(3)}(\psi)=\sum_{a,b}\prod_{i,j\in\mathbb Z/4}\rho_{AB}[(a_{ij},b_{ij}),(a_{i,j+1},b_{i+1,j})].$$

For the unscaled vertex $V=I-F$, define its row transfer by

$$T_{b,c}=\sum_{a\in\{0,1,2\}^4}\prod_{j\in\mathbb Z/4}V[(a_j,b_j),(a_{j+1},c_j)].$$

The contraction is $\operatorname{Tr}(T^4)/6^{16}$. The proof represents $T$ as an integer linear combination of the 24 coordinate permutations. Kernel-checked multiplication and convolution tables identify its fourth power; the permutation trace counts its fixed basis vectors and gives $-1680$.

## Falsifier

The claim would not be refuted if the translation convention, conjugation, normalization or arbitrary-finite-local-space quantifiers differed from Eq. (1.10). The public definitions retain the conventions of #17540. The last party is fixed, each other party translates its own replica coordinate, and the contraction includes every assignment exactly once. The witness has three local bases of size three and a normalization proved in the same module. No assumption about the desired sign is used.

## Evidence

The formal source is `D5/S3/Quantum/Information/MultiEntropyPositivityRefutation.lean`, with only the three public definitions `E`, `IsUnitState`, `claim` and the public theorem `result`. Private helpers prove normalization (`psi_unit`), the marginal (`rho_psi`), tracing and reindexing (`trace_party`, `E_torus`), row transfer (`Support.torus_transfer`, `Group.transfer_rep`), the integer trace (`Group.rep_four`, `Group.torus_value`), the exact value (`value`) and its sign (`negative`). These are internal checked steps, not additional public API theorems.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9). The publicized owners `SupportAndEdgeWordReflection.sum_fin_cons` and `LowRankRays.dot_star_self` have unfinished escape audits under [#17765](https://github.com/the-omega-institute/trureturing/issues/17765). No validated registration for either is claimed. Existing registrations of other owner theorems remain separate evidence.

The axiom closure of every public declaration is contained in `{propext, Classical.choice, Quot.sound}`. There is no atom or cover operation. The settling module has `admission_basis: open-problem-resolution (#17540; Refuted)`; its theorem and consumed private helpers are `proof_shape: bind-only`, with no escape witness claimed. Fixed-parameter certificates have `utility: kind=certified-instance` under `basis=refutes`.

### Experiment

The independent exact-arithmetic check is [the experiment directory at commit a8592536f8db2714b9646bd0b2147ff528a1d16d](https://github.com/the-omega-institute/trureturing-experiments/tree/a8592536f8db2714b9646bd0b2147ff528a1d16d/docs/reports/gadde-jain-krishna-kulkarni-sharma-2023-multi-entropy-positivity). From that checkout and directory, `python3 check.py` exits 0 with `ALL_OK`. The `check.py` SHA-256 is `b31c1a658566df80499542ca657eea13760612ebfc07dad02ad2621b45b5d523`. A rerun of those exact bytes gives the following readings.

The tested system is $q=3,n=4$, local marginal dimensions $3\times3$. At $s=1$ the row-transfer trace is $-1680$, independently for $I-F$ and the marginal traced from $\varepsilon$. The family polynomial is interpolated from the 17 exact samples $s=k/16$, $0\le k\le16$. Its degree is at most 16 because each transfer entry has degree at most four and the trace uses four transfers. Consequently those samples determine the polynomial exactly:

$$\begin{aligned}
P(s)={}&81s^{16}-432s^{15}+2808s^{14}-8976s^{13}+26460s^{12}-62640s^{11}\\
&+107208s^{10}-164880s^9+214758s^8-241680s^7+243144s^6\\
&-211248s^5+170748s^4-136080s^3+87480s^2-34992s+6561.
\end{aligned}$$

Sturm isolation reports one root in $[0,1]$, in $(0.8412640755539411,0.8412642045454546)$, and no root in $[9/10,1]$. The exact checks give $P(0)=6561$, $P(1)=-1680$, $P(9/10)=-3131320875975339759/10^{16}$ and $P(1/2)=32948241/65536$. The script also verifies the expansion of $P(1-u)$.

## Triage

Tier 1 published question; resolution: **Refuted**. Each claim below distinguishes kernel evidence, ordinary mathematical deductions, computation and open extensions.

### What the settlement shows

**Mechanism — kernel-checked.** `psi_unit` proves the normalized witness; `rho_psi` identifies its local kernel; `trace_party` and `E_torus` trace the fixed party and identify the periodic contraction. `Support.torus_transfer`, `Group.transfer_rep` and `Group.rep_four` establish the transfer evaluation. `value`, `negative` and the public `result` give the exact negative value and refutation.

**Transfer interpretation — proved in prose, not a Lean spectral theorem.** The swap $F$ is a self-adjoint involution. Thus $I-F$ has eigenvalues zero and two and is positive semidefinite. If the real transfer $T$ were Hermitian, its real eigenvalues would give $\operatorname{Tr}(T^4)=\sum\lambda^4\ge0$, contradicting $-1680$; the same argument excludes an entirely real spectrum. The obstruction is the spectrum of the periodic transfer, despite positive local vertices. Local positivity does not suffice for positivity of this torus contraction.

The $S_4$ interpretation uses the character identity $\operatorname{tr}_{\lambda}(T^4)=\sum_{p\in S_4}c_4(p)\chi_\lambda(p)$, with the coefficients of `Group.c4Data`. In cycle-type order $1^4,21^2,2^2,31,4$, their class sums are $786,-5024,2678,6912,-5336$. The four character rows are $(1,1,1,1,1)$, $(3,1,-1,0,-1)$, $(2,0,2,-1,0)$ and $(3,-1,-1,0,1)$. Their scalar products give the fourth-power traces below. Schur–Weyl hook-content multiplicities for dimension three give the second column; the length-four sign representation is absent. This is a finite character calculation in prose, not an additional formalized declaration.

| $S_4$ block | Multiplicity | Fourth-power trace |
| --- | ---: | ---: |
| $(4)$ | 15 | 16 |
| $(31)$ | 15 | −8 |
| $(22)$ | 6 | 16 |
| $(211)$ | 3 | −632 |

Hence $15\cdot16+15\cdot(-8)+6\cdot16+3\cdot(-632)=-1680$. Complex spectral phases permit the negative fourth-power contributions.

**Family — computed with the experiment above; not formalized.** For $0\le s\le1$, $\rho_s=(I-sF)/(9-3s)$ has $E_4^{(3)}=P(s)/(9-3s)^{16}$. The computed polynomial and root isolation give negativity exactly for $s_0<s\le1$, with $s_0$ in the displayed interval. The statement concerns this one-parameter family and this replica order.

**Purification and dimension — proved in prose, not formalized.** The symmetric and antisymmetric eigenspaces of $F$ have dimensions six and three, so $\rho_s$ has eigenvalues $(1-s)/(9-3s)$ and $(1+s)/(9-3s)$ with these multiplicities. They are positive for $0\le s<1$, and their weighted sum is one. Thus the negative interval contains full-rank marginals. Every purification has the same invariant because tracing its unshifted party leaves precisely $\rho_s$. Multiplicativity (source Eq. (1.12)) gives $E(\Psi_s^{\otimes k})=E(\Psi_s)^k$; odd positive $k$ preserve the negative sign and yield unbounded local dimensions. Even tensor powers have positive value. These arguments do not assert that the family exhausts all negative states.

**Consequences — proved in prose.** No real number has exponential equal to this negative $E$, so Eq. (1.11), read as a real logarithm, has no value on this state. A real-valued entropy requires a restricted domain or a changed definition/branch prescription. This refers to the source's logarithm, not to the totalized `Real.log` function in Lean. The coarse-graining inequalities (1.13)–(1.15), stated for $E$ itself, are separate assertions; this refutation proves no counterexample to them. Results requiring a real logarithm need its positive-domain condition.

**Nearest surviving statements and open questions.** For $n=2$, positivity has literature evidence in Penington–Walter–Witteveen arXiv:2211.16045, Eq. (2.6); it is not a theorem of this module. General positivity for $n=3$ is open here. The exact positive region among all states for $q=3,n=4$ is open; the computed one-parameter threshold is not that classification. Gadde–Jain arXiv:2406.17447, Remark III.3, gives a reflection-positive subclass. Whether reflection-positive invariants are exactly the positive ones remains open here. Coarse-graining monotonicity and the $n\to1$ continuation are not settled.

**Literature.** The readings in Gap and #17540 report no negative value of $E_n^{(q)}$ in their searched scope; worldwide completeness and priority remain `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

The literature search is bounded and does not establish exhaustive worldwide novelty. The spectral interpretation, full-rank family, purification argument, tensor-power extension and consequences for the real logarithm are not Lean theorems of this delivery; their evidence kinds and scopes are stated in Triage. No conclusion is claimed for all replica orders or for coarse-graining monotonicity. The two owner escape audits remain unfinished under #17765.
