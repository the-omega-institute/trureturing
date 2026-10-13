---
slug: quinta-andre-burchardt-zyczkowski-2019-m-resistant-states
bibkey: quinta2019resistant
doi: 10.1103/PhysRevA.100.062329
url: https://arxiv.org/abs/1908.10390v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/MResistantQuditExistence.result
---

# M-resistant qudit states exist for every admissible loss parameter

## Problem

Quinta, André, Burchardt and Życzkowski, *Cut-resistant links and multipartite entanglement resistant to particle loss*, Phys. Rev. A 100, 062329 (2019), arXiv:1908.10390v1, Section V, state:

> **Conjecture.** For any $N$ and $m$, there exists an $m$-resistant $N$-qudit state in some local dimension $d$.

Their Section III definition says that an entangled state remains entangled after tracing out any $m$ subsystems and becomes separable after tracing out any $m+1$ subsystems. This dossier uses finite full separability for the separable predicate and the admissible range $N\geq3$, $m+2\leq N$.

### Statement echo

The Lean `claim` quantifies all natural $N,m$ with $3\leq N$ and $m+2\leq N$, then supplies a natural local dimension $d$, a pure amplitude function on $(\mathrm{Fin}\,N)\to\mathrm{Fin}\,d$, unit norm by the finite sum of `Complex.normSq`, and `IsMResistant m ψ`. `IsMResistant` is the conjunction of initial failure of full separability, failure after every loss set of cardinality $m$, and full separability after every loss set of cardinality $m+1$. The pure-state convention is the frozen `rankOneDensity` declaration.

## Motivation

The source leaves existence in some local dimension open for the full admissible range. Zhang, Han, Shi and Zhang, arXiv:2505.06567v1, Conjecture 1, restate the same existence question. Han, Zhang and Zhang, arXiv:2606.08561v1, still report only the range $m\leq (N-2)/2$ as known. The frozen declaration `D5/S3/Quantum/Entanglement/MResistantQuditExistence.result` proves the source conjecture in its stated admissible range.

## Gap

The kernel-checked construction in `MResistantQuditExistence.result` uses the full local carrier `Finset (Fin N) × Bool`, carried to `Fin d`, with $d=2^{N+1}$. The source conjecture asks only for existence in some dimension, so this closes its quantified claim. The restricted-label construction below proves in prose that dimension $2\binom{N}{m}$ suffices. This is separate from the kernel-checked witness. The least possible local dimension is not determined here. Qubit constructions for $m>(N-2)/2$ and the minimal local dimension remain open.

The literature screen in preregistration #15010 is bounded to the cited source, Zhang et al. (2025), Han et al. (2026), and its recorded searches; it supports `not-found-in-searched-scope` and does not assert exhaustive worldwide priority. The escape audit is unfinished under issue [#15589](https://github.com/the-omega-institute/trureturing/issues/15589). Its concrete gap is a faithful dependent-family registration with full source reconstruction and equivalence bridge, actual-positive law, whole-family variation, independent sensitivity, and observational-dependence evidence. The delivered-head DTR reading is `DTR-Unregistered` (Observe) for `separable_exchange_zero` and `result`; no `declared_validated` registration is claimed.

## Route

Let $k=N-m$. Encode each $k$-subset $S$ together with a bit. Every site records the common subset label, and the bit is recorded only at sites in $S$. The local carrier is `Finset (Fin N) × Bool`, and `Fintype.equivFin` carries it to a finite local basis of size $d=2^{N+1}$. Only $k$-subset labels occur in the state support. The state is the uniform superposition of the resulting distinct product-basis configurations.

A loss of $m+1$ sites meets every $k$-subset, so all off-diagonal terms disappear. The remaining diagonal is a finite convex mixture of products of local basis projectors and is fully separable. A loss of $m$ sites leaves exactly one intact flag. Its surviving coherence has a zero exchanged diagonal; `separable_exchange_zero` rules out full separability. The same exchanged-diagonal obstruction gives initial entanglement.

### Restricted local dimension: proved in prose

Assume $N,m$ are natural numbers with $N\geq3$ and $0\leq m\leq N-2$. Put $V=\{0,\ldots,N-1\}$, $k=N-m\geq2$, and $\mathcal E=\{S\subseteq V:|S|=k\}$. Since $k\leq N$, the number $s=|\mathcal E|=\binom Nk=\binom Nm$ is positive. Take the same local Hilbert space at every site, with orthonormal basis $\{|S,b\rangle:S\in\mathcal E,\ b\in\{0,1\}\}$. Its dimension is $d=2s=2\binom Nm$. For $S\in\mathcal E$ and $b\in\{0,1\}$, define the product-basis word

$$
|w_{S,b}\rangle=\bigotimes_{i\in V}|S,b\,\mathbf1_{i\in S}\rangle,
\qquad
|\psi_{\mathcal E}\rangle=\frac1{\sqrt{2s}}\sum_{S\in\mathcal E}\sum_{b=0}^1|w_{S,b}\rangle.
$$

1. **Normalization and restriction.** If $S\ne T$, the common subset labels distinguish $w_{S,b}$ and $w_{T,c}$ at every site. For fixed $S$, its two bit words differ at any site in the nonempty set $S$. Thus the $2s$ words are distinct orthonormal product-basis vectors, and $\|\psi_{\mathcal E}\|^2=(2s)/(2s)=1$. Let $H_{\mathrm{all}}$ have basis all $(S,b)$ with $S\subseteq V$, and let $U:H_{\mathcal E}\to H_{\mathrm{all}}$ send each restricted basis vector to the identically labelled full basis vector. It is an isometry. Every amplitude of the full-carrier flag state outside these words is zero, so $U^{\otimes N}\psi_{\mathcal E}$ is exactly that full-carrier state, before the bijective enumeration of its basis by $\mathrm{Fin}\,2^{N+1}$. Restriction retains every summand and its normalization coefficient; no projection with subsequent renormalization is needed.

2. **Partial traces commute with this restriction.** For any lost set $J\subseteq V$ and retained set $R=V\setminus J$, write $\rho_{\mathcal E,J}=\operatorname{Tr}_J|\psi_{\mathcal E}\rangle\langle\psi_{\mathcal E}|$. Tracing a matrix unit $|w_{S,b}\rangle\langle w_{T,c}|$ multiplies its retained matrix unit by $\prod_{j\in J}\langle T,c\mathbf1_{j\in T}|S,b\mathbf1_{j\in S}\rangle$. The isometry preserves each such inner product. Hence, by linearity, the full-carrier marginal equals $U_R\rho_{\mathcal E,J}U_R^*$, where $U_R=\bigotimes_{i\in R}U$; full-basis trace terms with a lost label outside $\mathcal E$ contribute zero. This identity also holds for $J=\varnothing$, when the empty product equals one.

3. **Full separability is preserved in both directions.** A finite convex mixture of products of local positive trace-one matrices on $H_{\mathcal E}$ maps under $U_R$ to such a mixture on $H_{\mathrm{all}}$, because each local map $\sigma\mapsto U\sigma U^*$ preserves positivity and trace. Conversely, suppose $U_R\rho U_R^*$ is fully separable and $\rho$ is a density matrix on $H_{\mathcal E}^{\otimes R}$. Write a finite product decomposition with weights $p_a\geq0$ summing to one and local density matrices $\sigma_{a,i}$. Set $P=UU^*$ and $Q=I-P$. Its marginal at every site $i\in R$ is supported in $P$, so $0=\sum_a p_a\operatorname{Tr}(Q\sigma_{a,i})$. All summands are nonnegative. For each $p_a>0$, therefore, $\operatorname{Tr}(Q\sigma_{a,i})=0$. Positivity implies $\sigma_{a,i}=P\sigma_{a,i}P$: the zero diagonal entries on an orthonormal basis of $Q$ force the corresponding rows and columns to vanish by the positive two-by-two minor inequality. Thus $U^*\sigma_{a,i}U$ is positive with trace one. Discarding zero-weight terms and compressing every remaining factor gives a finite fully separable decomposition of $\rho$. All marginals used below have at least one retained site. This proves that reducing the local carrier cannot change their full-separability status.

4. **Every $(m+1)$-particle loss is fully separable.** Assume $|J|=m+1$, so $J\ne\varnothing$ and $|R|=k-1$. Different subset labels are distinguished on any lost site. For equal subset labels $S$, the two bit branches are distinguished on a lost site as well: otherwise $S\subseteq R$, contradicting $|S|=k>|R|$. Consequently only terms with $(S,b)=(T,c)$ survive the trace, and

$$
\rho_{\mathcal E,J}=\frac1{2s}\sum_{S\in\mathcal E}\sum_{b=0}^1
|w^R_{S,b}\rangle\langle w^R_{S,b}|.
$$

Here $w^R_{S,b}=w_{S,b}|_R$ denotes the restriction of the word to retained sites. Each summand is a product of local basis projectors of trace one; the $2s$ nonnegative weights sum to one. This is an explicit fully separable decomposition, even if some retained words coincide.

5. **Every $m$-particle loss is entangled.** Assume $|J|=m$, so $|R|=k\geq2$ and $R\in\mathcal E$. Let $x=w_{R,0}|_R$ and $y=w_{R,1}|_R$. A summand having retained word $x$ must have label $R$, and then branch zero; a summand having retained word $y$ must have label $R$, and then branch one. These two full words agree on every site of $J$ (their bit is zero there), so $\rho_{\mathcal E,J}(x,y)=1/(2s)\ne0$. Choose distinct $i,j\in R$. Exchange the $i$-th entries of $x$ and $y$, obtaining $u$ and $v$. Both exchanged words still have the common label $R$, but their bits at $i$ and $j$ differ. No supported word restricts to $u$ or $v$: its label would force $S=R$, whose branch bit is constant on $R$. Hence both exchanged diagonal entries are zero. The implication proved by `FullySeparableExchangeObstruction.separable_exchange_zero` applies to these finite local carriers: a fully separable matrix with a zero exchanged diagonal has zero original coherence. To see the implication directly, in a product decomposition each weighted exchanged-diagonal term is nonnegative; a zero sum forces each positively weighted product to have a zero local diagonal factor. Positivity annihilates that factor's row or column, including the corresponding coherence factor. Thus all original coherence summands vanish, a contradiction. This proves nonseparability of the marginal. When $m=0$, $J=\varnothing$ and $R=V$; the same coherence and exchanged-diagonal computation applies without suppressing cross-label terms by a trace.

6. **Initial entanglement.** Choose any $S\in\mathcal E$ and set $x=w_{S,0}$, $y=w_{S,1}$. Their pure-density coherence is $1/(2s)$. Since $k\geq2$, exchanging a site in $S$ gives words with unequal bits at two sites of $S$. Such words are absent from the support, so their pure-density diagonals vanish. The same full-separability implication used in step 5 proves that $|\psi_{\mathcal E}\rangle\langle\psi_{\mathcal E}|$ is entangled. Together with steps 1, 4 and 5, this proves an $m$-resistant state in dimension $2\binom Nm$ for every stated admissible pair. Enumerating the restricted orthonormal basis by $\mathrm{Fin}\,d$ is a local unitary relabeling and preserves these properties.

**Evidence kind:** proved in prose. The restricted-dimension conclusion and the isometry argument above are not additional kernel-checked declarations. The kernel-checked `MResistantQuditExistence.result` retains its witness on the full carrier of dimension $2^{N+1}$. The prose construction supplies an upper bound $2\binom Nm$ on the least admissible local dimension; its optimal value and qubit existence for $m>(N-2)/2$ remain open.

## Falsifier

A counterexample would be an admissible pair $(N,m)$ for which every finite local dimension fails to provide a normalized pure state satisfying the three resistance clauses, or a failure of one of the universal loss-set clauses for the displayed construction. The kernel-checked result covers all natural $N,m$ in the claim's range. A qubit-only counterexample outside that range would not refute the settled claim.

## Evidence

The supporting declaration `D5/S3/Quantum/Entanglement/FullySeparableExchangeObstruction.separable_exchange_zero` has declaration statement ID `sha256:cc9db09ebb15605032c0bc389540ec1e76e4442c2d71fdc283cde133048236a2`. The settling declarations have declaration statement IDs `sha256:1327de9bec1f4dd508480f4407987fe29f8fc10c5d9ea9fb2b41f0ed887faa6b` for `IsMResistant`, `sha256:7d826234e720b0c2efc25eaac6761eee1912e871a92f4c99589597d27d7cd5ad` for `claim`, and `sha256:57e94cd6f0c4b6a84a1ae0d8066ee21cce8b203557c717e0a3f2ad90f98b2e6c` for `result`. The settling module state pin is `sha256:cc99e7d4b3509064bf7c9ba23b3a83bcdf0858f728cfe0ce70f3b5f31418998d`.

The kernel axiom closure of every public declaration is contained in `{propext, Classical.choice, Quot.sound}`. The frozen prerequisites used by the settling proof are `D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity`, `D5/S3/Quantum/Entanglement/LocalObservationPartialTraceEquivalence.partialTraceFirst`, `D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState`, and `D5/S3/Quantum/Information/OrthogonalRecordEntropy.pointerState`; the supporting obstruction is a same-delivery prerequisite.

The exact-rational reading is published at [`docs/reports/quinta-andre-burchardt-zyczkowski-2019-m-resistant-states/check.py`](https://github.com/the-omega-institute/trureturing-experiments/tree/664831fdc0f2267cd539af109024ede9e42826ab/docs/reports/quinta-andre-burchardt-zyczkowski-2019-m-resistant-states) in commit `664831fdc0f2267cd539af109024ede9e42826ab`. The command `python3 check.py` exits `0`, ends with `ALL_OK`, and checks $3\leq N\leq6$ with exact rational entries. The script SHA-256 is `c25ee3e55a0028bdabbeffd0e80e260e26022c08bd59b97cf359d319e9f1bb70`.

## Triage

| Item | Status | Evidence and boundary |
| --- | --- | --- |
| Flag-code every $k=N-m$ subset with a shared label and a bit localized to that subset; every $(m+1)$-loss is diagonal and fully separable; every $m$-loss retains an obstruction coherence. | proved | `MResistantQuditExistence.result` is kernel-checked; `separable_exchange_zero` supplies the exchanged-diagonal implication. |
| Local dimension of the kernel witness. | proved | Kernel-checked: `MResistantQuditExistence.result` chooses the cardinality of `Finset (Fin N) × Bool`, namely $d=2^{N+1}$. |
| Restricted-label local dimension $d=2\binom{N}{m}$. | proved | Proved in prose in “Restricted local dimension”: normalization, isometric restriction and partial-trace compatibility, full-separability equivalence, every loss clause, and initial entanglement. This dimension is not a kernel-checked witness. |
| Exact finite reading. | computed | `python3 check.py`, exit `0`, script SHA-256 `c25ee3e55a0028bdabbeffd0e80e260e26022c08bd59b97cf359d319e9f1bb70`, scope $3\leq N\leq6$ and $0\leq m\leq N-2$, exact rational density entries and floating-point partial-transpose eigenvalues, final line `ALL_OK`. |
| Qubit states for $m>(N-2)/2$. | open | The construction uses larger local dimensions; no qubit existence result in this range is claimed. |
| Minimal local dimension. | open | The prose construction gives the upper bound $2\binom{N}{m}$; no optimality theorem or further lower bound is proved. |

### What the settlement shows

The decisive mechanism is the shared subset label plus a localized branch bit. It works uniformly for every admissible natural $N,m$ and yields the kernel-witness dimension $2^{N+1}$. The proof extends the source's known range $m\leq(N-2)/2$ to the whole pure-state existence conjecture in arbitrary local dimension. The separate prose proof reduces the sufficient dimension to $2\binom{N}{m}$. Neither proof settles qubit existence beyond that known range or determines the minimal local dimension. The source's ordinary resistance statements remain compatible: this result supplies the existence premise in the full admissible range, while minimal dimension and qubit-specific questions remain separate.

The public result is the settling result for the named open problem and is admitted under `open-problem-resolution (#15010; Proved)`. The escape audit remains unfinished under #15589 with the `DTR-Unregistered` reading above; no `declared_validated` registration is claimed.

## ASSUMED-UNVERIFIED

The Lean kernel verifies the formal finite-dimensional statement and its standard axiom closure. The correspondence between the formal predicates and the source's physical terminology, the quoted literature statements, and completeness of the bounded literature screen are external assumptions. The exact-rational experiment is evidence only for $3\leq N\leq6$ and does not replace the uniform Lean proof.
