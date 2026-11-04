---
slug: davalos-ziman-pineda-2019-qutrit-divisibility-entanglement-breaking
bibkey: davaloszimanpineda2019divisibility
doi: 10.22331/q-2019-05-20-144
url: https://arxiv.org/abs/1812.11437v4
triage: theorem
motivation_gids:
  - D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.result
---

# Divisibility does not force entanglement breaking for qutrits

## Problem

D. Davalos, M. Ziman and C. Pineda, *Divisibility of qubit channels and dynamical maps*, Quantum 3, 144 (2019), arXiv:1812.11437v4, ask in the abstract:

> Finally, we show that every divisible but not infinitesimal divisible qubit channel (in positive maps) is entanglement breaking, and open the question if something similar occurs for higher dimensions.

This sentence is in the source TeX `paper.tex`, lines 162–164. In Section 2.1 the authors define a divisible channel by the negation of indivisibility, where indivisibility means that a concatenation into two channels forces one factor to be unitary (lines 256–261). In Section 2.2 they write:

> we say $\mathcal E\in\mathsf C^P$ if there exists a P-divisible dynamical map $\mathcal E_t$ such that $\mathcal E=\mathcal E_t$ (with arbitrary precision) for some value of $t$ (including $t=\infty$).

This is lines 337–339. Theorem 6 states:

> Consider a qubit channel $\mathcal E$. If $\det\hat\mathcal E<0$, then $\mathcal E$ is entanglement breaking, i.e. all qubit channels outside $\mathsf C^P$ are entanglement breaking.

This is lines 1237–1241. The settled qutrit reading is the assertion that every completely positive trace-preserving qutrit map that is divisible and outside the formal `pDivisibleSet` is entanglement breaking. The module names this assertion `claim`.

## Motivation

The qubit theorem makes entanglement breaking a consequence of being outside the P-divisible set. If the same implication held for qutrit channels, the higher-dimensional question in the abstract would have a positive answer at dimension three. A qutrit counterexample tests the implication at the first dimension beyond the paper’s theorem and separates divisibility from entanglement breaking.

## Gap

The bounded literature check recorded in issue [#23296](https://github.com/the-omega-institute/trureturing/issues/23296) found no settlement in its searched scope. Semantic Scholar listed 37 citing works; the divisibility-related works identified there, including arXiv:2203.13451, arXiv:2009.06666, arXiv:1911.09468, arXiv:1908.05702 and arXiv:2505.08785, address other questions. The searched abstracts of arXiv:2203.13451 and Davalos’s thesis arXiv:2009.00159 do not settle entanglement breaking of higher-dimensional divisible channels outside $\mathsf C^P$. Repository searches found no earlier matching issue or declaration. `not-found-in-searched-scope`.

## Route

The module works with complex-linear maps `MatrixMap (Fin 3) (Fin 3) ℂ`. Its definitions are:

- `IsUnitaryChannel t` means that there is $U$ in `Matrix.unitaryGroup (Fin 3) ℂ` such that, for every matrix $X$, $tX=UXU^\ast$.
- `IsDivisible t` means that there are maps $t_1,t_2$ with `IsCPTP t₁`, `IsCPTP t₂`, `t = t₁.comp t₂`, and neither factor is an `IsUnitaryChannel`.
- `IsPositiveTP v` means $X\succeq0\Rightarrow vX\succeq0$ for every $X$, together with `v.IsTracePreserving`.
- `IsPDivisibleMap e` requires $e(0)=\mathrm{id}$, `IsCPTP (e t)` for every $t\ge0$, continuity of $t\mapsto$ `transferMatrix (e t)` on $[0,\infty)$, and, for every $0\le t<s$, a map $v$ with `IsPositiveTP v` and either `e s = v.comp (e t)` or `e s = (e t).comp v`.
- `pDivisibleSet` consists of maps whose transfer matrices lie in the topological closure of the transfer matrices of all endpoints $e(t)$ with `IsPDivisibleMap e` and $0\le t$.
- `IsEntanglementBreaking t` requires, for every $n\in\mathbb N$ and every $\rho$ on $\mathrm{Fin}\,n\times\mathrm{Fin}\,3$, that positive semidefinite trace-one $\rho$ is sent by `MatrixMap.kron (LinearMap.id) t` into `separableCone`.

The channel is
$W(X)=\tfrac12\bigl(\operatorname{tr}(X)I-X^{\mathsf T}\bigr),\quad D(X)=\tfrac12X+\tfrac16\operatorname{tr}(X)I,\quad T=D\circ W.$
The private lemmas `wernerHolevo_one_eq_kraus` and `depolarized_one_eq_kraus` identify the two maps with the displayed Kraus families. The completeness identities `wk_complete` and `dk_complete` feed `w_cptp` and `d_cptp`; `t_cptp` proves `IsCPTP t` by the frozen `cp_comp` (complete positivity is preserved by composition) and the two trace-preservation identities. The formula lemmas `w_formula`, `d_formula` and `t_formula` establish the displayed actions.

The purity identity `unitary_purity` applies to every unitary $U$ and the input matrix unit $E_{00}$. Comparing it with the explicit outputs proves `w_not_unitary` and `d_not_unitary`. The lemma `t_divisible` then supplies `IsDivisible t` with factors $D$ and $W$, including their `IsCPTP` and non-unitarity hypotheses.

For the P-divisible obstruction, `cptp_hermiticity` states that if `hT : IsCPTP T`, then every $X$ satisfies $T(X^\ast)=T(X)^\ast$. The lemma `hermiticity_preserving_det_real` uses the hypothesis $\forall X,\ T(X^\ast)=T(X)^\ast$ to prove that the imaginary part of $\det(\mathrm{transferMatrix}\ T)$ is zero. The lemma `pdivisible_endpoint_det_nonneg` has the exact hypotheses `hE : IsPDivisibleMap E`, $u:\mathbb R$, and `hu : 0 ≤ u`; it concludes
$\operatorname{Im}\det(\mathrm{transferMatrix}(E(u)))=0\text{ and }0\le\operatorname{Re}\det(\mathrm{transferMatrix}(E(u))).$
Its proof uses `hE`’s channel, continuity and propagator clauses, the intermediate value theorem, and the factorization at $0\le z<u$ supplied by the two-sided composition alternative in `IsPDivisibleMap`. The zero determinant at the intermediate time is propagated to $u$ by `Matrix.det_mul`.

The closure argument is `pdivisibleSet_subset_nonnegativeDet`: the set of transfer matrices with zero imaginary determinant and nonnegative real determinant is closed, and every endpoint satisfies it by `pdivisible_endpoint_det_nonneg`. The entry calculation `transfer_entry` and block determinant calculation `t_det` give
$\det(\mathrm{transferMatrix}\ t)=-\left(\tfrac14\right)^8.$
Thus `t_not_pdivisible` proves that `t` is not in `pDivisibleSet`.

Finally, `omega_density` proves that `maxEntangled (Fin 3)` is positive semidefinite and has trace one. The exact calculation `witness_partial_transpose_negative` gives the real quadratic value $-1/9$ of the partial transpose of the amplified output on the maximally entangled vector. If the output were in `separableCone`, `separableCone_partialTranspose_posSemidef` would make that quadratic value nonnegative. This contradiction is `t_not_entanglementBreaking`. The theorem `result` applies `claim` to $t$ using `t_cptp`, `t_divisible` and `t_not_pdivisible`, then invokes `t_not_entanglementBreaking`.

## Falsifier

The refutation would not match the source question if the formal predicates changed its quantifiers or channel class. Here the factorization is exactly `t = t₁.comp t₂` with both factors completely positive and trace preserving and both non-unitary. The formal P-divisibility condition allows a positive trace-preserving propagator on either composition side and does not require `e t` to be invertible; its endpoint closure therefore contains the source’s P-divisible endpoints under either reading of the source’s inverse propagator. Non-membership in this wider set is a stronger exclusion. The formal entanglement-breaking predicate quantifies over every natural ancillary dimension and every positive semidefinite trace-one input, and uses the separable cone for the amplified output.

The witness is the composition of the source-compatible Werner–Holevo map at parameter $1$ with the depolarizing map at parameter $1/2$. The determinant obstruction and the negative partial-transpose quadratic value target exactly the formal `pDivisibleSet` and `IsEntanglementBreaking` definitions.

## Evidence

The canonical source is `D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.lean.json`.

Declaration statements:
- `result`: `sha256:731f67ec7a21c4e90790b0dbda23f58c28a26288bf20bd8cbb0ba302f201bfc5`;
- `claim`: `sha256:71715d1e40af5b188e5f22653e714d91d17b855b9c5bed81982b131f8d2ddead`.

## Triage

Tier 1: an explicit higher-dimensional question in the abstract of the 2019 *Quantum* paper, preregistered in issue #23296 before any Lean.

`theorem`; resolution `refuted`.

Every declaration is bind-only. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that every qutrit map $t$ satisfying `IsCPTP t`, `IsDivisible t`, and `t ∉ pDivisibleSet` satisfies `IsEntanglementBreaking t`.

**Computed, not formalized:** the floating-point checks of the counterexample that the orchestrator recorded in #23296 (the composition, the determinant of $T$, the Choi spectrum and its partial transpose, and the positivity of the two factors) agree with the formal statement.

**Argued, not formalized.**

- The failure mechanism is a determinant sign obstruction: the formal route keeps P-divisible endpoint determinants real and nonnegative, while the divisible witness has negative determinant, and its partial transpose has a negative quadratic value incompatible with separability.
- The missing structure is the qubit-specific link from a negative determinant to entanglement breaking: in the qutrit formalization, the determinant sign excludes the P-divisible endpoint closure but does not itself force membership in the separable cone.
- The source’s qubit Theorem 6 and its separate statements about the L-divisible and CP-divisible sets are outside this qutrit assertion and are unaffected. A higher-dimensional statement that would imply the settled universal qutrit claim is refuted at dimension three.
- The oracle report recorded in issue #23296 argues for the family $T_s=D_s\circ W$ for $1/4<s\le1/2$ and for an extension to every dimension $d\ge3$; those family and all-dimension assertions are open here because they are not formalized.

## ASSUMED-UNVERIFIED

The literature check is bounded to the sources and repository searches recorded in issue #23296 and does not establish exhaustive worldwide novelty or priority. The numerical checks and the family and all-dimension extensions in “Computed, not formalized” and “Argued, not formalized” are not Lean results. The module does not formalize the source’s qubit theorem, its converse questions, or its L-divisible and CP-divisible classifications. Any source statement beyond the passages reproduced above remains assumed-unverified here.
