---
slug: seshadri-leditzky-siddhu-smith-2023-signalling-game-values
bibkey: seshadrileditzkysiddhusmith2023signalling
doi: 10.1109/TIT.2023.3274434
url: https://arxiv.org/abs/2205.13538v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/SignallingGameValueEquality.result
---

# The signalling game has equal classical, quantum and no-signalling values

## Problem

A. Seshadri, F. Leditzky, V. Siddhu and G. Smith, *On the separation of correlation-assisted sum capacities of multiple access channels*, arXiv:2205.13538v3 (2023), Section 3.2.1, define the signalling game using question sets $\mathcal X_1$ and $\mathcal X_2$, answers $\mathcal Y_1=\mathcal X_2$ and $\mathcal Y_2=\mathcal X_1$, and the winning condition

> Formally, we consider question sets $\mathcal{X}_1$, $\mathcal{X}_2$ and answer sets $\mathcal{Y}_1 = \mathcal{X}_2$ and $\mathcal{Y}_2 = \mathcal{X}_1$, and the winning condition is defined as $\mathcal{W} = \{(x_1, x_2, y_1, y_2) \in (\mathcal{X}_1 \times \mathcal{X}_2) \times (\mathcal{Y}_1 \times \mathcal{Y}_2) \mid y_1 = x_2,\ y_2 = x_1\}$.

The source proves the classical value $1/\max(|\mathcal X_1|,|\mathcal X_2|)$ and then asks whether the quantum and no-signalling values coincide with it. Its Section 3.2.1, line 880, states:

> For $2 \leq |\mathcal{X}_1|, |\mathcal{X}_2| \leq 10$, we verify that the numerically computed value for $\omega^{\text{NS}}(G_{\text{s}})$ matches $\omega^{\text{cl}}(\mathcal{N}_{G_{\text{s}}}) = 1/\max(|\mathcal{X}_1|, |\mathcal{X}_2|)$. Thus, we expect $\omega^{\text{cl}}(\mathcal{N}_{G_{\text{s}}}) = \omega^{\text{Q}}(\mathcal{N}_{G_{\text{s}}}) = \omega^{\text{NS}}(\mathcal{N}_{G_{\text{s}}})$ for the signalling game.

The preregistration reads this as the finite-game value question for $m=|\mathcal X_1|\ge1$ and $n=|\mathcal X_2|\ge1$, with uniformly drawn questions.

## Motivation

The signalling game is the example used by the source to separate unrestricted communication from classical, quantum-assisted and no-signalling-assisted sum rates of a multiple-access channel. The classical value tends to zero as the question alphabets grow, while the communication-assisted value can remain perfect. Establishing the same sharp game value for quantum and no-signalling strategies supplies the missing game-theoretic equality behind the source's proposed stronger separation, while the associated channel-capacity statements remain separate claims.

## Gap

The literature check recorded in issue [#22482](https://github.com/the-omega-institute/trureturing/issues/22482) found the expectation in the v3 TeX and the source's numerical linear-program checks for $2\le m,n\le10$, but no proof for arbitrary finite question sets. The search also found the two-player guess-your-neighbour's-input literature, including binary-input results, without finding the equality for arbitrary unequal question-set sizes. The issue records nine citing works screened and no repository, MathDB or formal-conjectures settlement.

`not-found-in-searched-scope`.

## Route

1. **No-signalling upper bound.** For `{m n : \mathbb N}`, a box `p : Fin n → Fin m → Fin m → Fin n → \mathbb R`, hypotheses `hm : 1 ≤ m`, `hn : 1 ≤ n` and `hp : IsNoSignalling p`, the private lemma `noSignalling_bound` proves `winProb p \le 1 / (max m n : \mathbb R)`. From the nonnegativity and the two marginal equalities in `IsNoSignalling`, each winning term is bounded by a corresponding marginal term. The winning sum is therefore at most $m$ by the Alice-marginal calculation and at most $n$ by the Bob-marginal calculation. The proof uses the witnesses `xzero : Fin m` and `yzero : Fin n` supplied by the two nonemptiness hypotheses, and then splits on $m\le n$ or $n\le m$.
2. **Quantum-to-no-signalling inclusion.** For `{m n da db : \mathbb N}`, `rho : Matrix (Fin da × Fin db) (Fin da × Fin db) \mathbb C`, `a : Fin m → Fin n → Matrix (Fin da) (Fin da) \mathbb C`, `b : Fin n → Fin m → Matrix (Fin db) (Fin db) \mathbb C`, and the hypothesis `hs : IsQuantumStrategy rho a b`, the private lemma `quantum_noSignalling` proves `IsNoSignalling (quantumBox rho a b)`. Summing each local POVM over its answers gives the identity; positivity of the state and effects gives nonnegative Born probabilities, normalization gives total mass one, and the resulting marginal traces are independent of the other question.
3. **A deterministic witness in the quantum class.** For `{m n : \mathbb N}` and any response functions `fa : Fin m → Fin n` and `fb : Fin n → Fin m`, the private lemma `deterministic_quantum` constructs a one-dimensional density matrix and one-dimensional diagonal POVMs and proves `quantumBox rho a b = deterministicBox fa fb`.
4. **Sharp deterministic value.** For `{m n : \mathbb N}` under hypotheses `hm : 1 ≤ m` and `hn : 1 ≤ n`, the private lemma `optimal_deterministic` constructs response functions by reducing indices modulo the target dimension and proves `winProb (deterministicBox fa fb) = 1 / (max m n : \mathbb R)`. Its two cases are $m\le n$, where the smaller side contributes $m$ winning pairs, and $n\le m$, where it contributes $n$.
5. **Assembling the greatest elements.** `result` applies the deterministic witness, its quantum realization and `quantum_noSignalling` to obtain members attaining the target value. It applies `noSignalling_bound` to every no-signalling witness, to every quantum witness after the quantum-to-no-signalling conversion, and to every classical deterministic witness after the one-dimensional quantum embedding. These membership and upper-bound statements give the three `IsGreatest` conjuncts in `claim`.

## Falsifier

The settlement would not address the source question if the formal game changed any of the following: the answer types $\mathrm{Fin}\,n$ and $\mathrm{Fin}\,m$, the winning entries `p y x x y`, the uniform factor $1/((m:\mathbb R)n)$, or either no-signalling marginal condition. It would also fail to match the quantum part if `IsQuantumStrategy` did not require a finite-dimensional density matrix and a POVM for every local question, or if `quantumBox` did not use the real part of Born's rule for the Kronecker product of the two effects.

The module's `classicalValues` is exactly the set generated by deterministic functions `Fin m → Fin n` and `Fin n → Fin m`. The source explains in Section 2 that, for uniformly drawn questions, a classical optimum can be taken deterministic; that reduction is part of the source reading rather than a separate theorem in this module. The source's notation $\omega(\mathcal N_{G_{\mathrm s}})$ at line 880 is read through the surrounding text as the signalling-game value; the formal claim uses the explicitly defined game-value sets.

## Evidence

The canonical source is `D5/S3/Quantum/Information/SignallingGameValueEquality.lean`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/SignallingGameValueEquality.lean.json`.

Declaration statements:
- `result`: `sha256:f8af4cadb01807240a121e8f14b27293a64ec5a36b9df0374976ddaec90d3a71`;
- `claim`: `sha256:90cfbc844676f34bbf2d5c81af6a4ee8c12c045c844c6e5166c17423ba17da99`.

- **Definitions.** It defines `IsNoSignalling`, `winProb`, `deterministicBox`, `classicalValues`, `IsQuantumStrategy`, `quantumBox`, `quantumValues`, `noSignallingValues` and `claim`, and proves `result : claim`.
- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 expectation of a 2023 *IEEE Transactions on Information Theory* paper, preregistered in issue #22482 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $m,n:\mathbb N$ with $1\le m$ and $1\le n$, each of `noSignallingValues m n`, `quantumValues m n` and `classicalValues m n` has greatest element $1/(\max(m,n):\mathbb R)$.

**Computed, not formalized**

- Seshadri, Leditzky, Siddhu and Smith (2023) find numerically computed no-signalling values matching $1/\max(|\mathcal X_1|,|\mathcal X_2|)$ throughout the range $2\le|\mathcal X_1|,|\mathcal X_2|\le10$.

**Argued, not formalized**

- The source's later statement that the equality would force $S_{\mathrm Q}(\mathcal N_{G_{\mathrm s}})$ and $S_{\mathrm{NS}}(\mathcal N_{G_{\mathrm s}})$ to tend to zero while $C(\mathcal N_{G_{\mathrm s}})$ tends to infinity now has its finite-game equality premise supplied by `result`, but the channel-capacity definitions, bounds and limiting argument are not formalized here and remain open.
- The result is sharp for every nonempty pair of finite question sets in the module's model because `IsGreatest` includes both attainment and the universal upper bound. Whether the equality persists for nonuniform question distributions, more than two players, infinite-dimensional strategies, or different winning predicates is open here.
- The source's classical deterministic reduction and its sum-capacity consequences are not re-proved by this declaration; they affect the source's dependent claims only through the unformalized bridges just identified.

## ASSUMED-UNVERIFIED

The literature check is bounded by the sources and citing works recorded in issue #22482 and does not establish exhaustive worldwide novelty or priority. The numerical checks reported by the source are not formalized. The source's reduction from general uniformly sampled classical strategies to deterministic strategies, the channel construction $\mathcal N_{G_{\mathrm s}}$, and all capacity and asymptotic statements are outside `claim` and remain unverified in Lean. Statements about nonuniform distributions, larger player numbers, infinite dimensions and other games are not settled by this dossier.
