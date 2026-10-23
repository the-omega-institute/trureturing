---
slug: ghosh-konar-francica-pal-sen-de-2025-stabilizer-battery-degree-difference-refutation
bibkey: ghoshkonarfrancicapalsende2025stabilizer
doi: null
url: https://arxiv.org/abs/2512.22908v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/StabilizerBatteryDegreeDifferenceRefutation.result
---

# The work stored in a stabilizer battery is not a function of the degree difference

## Problem

D. Ghosh, T. K. Konar, G. Francica, A. K. Pal and A. Sen(De), *Quantum advantage unlocked: Charging quantum batteries with K-regular graph stabilizers*, arXiv:2512.22908v2, Section III, Remark:

> While our initial investigation with $N\leq 10$ indicates that $W_{(N,K^\prime,K)}$ remains unchanged as long $\Delta = |K-K^{\prime}|$ is constant for $N\neq 4N^\prime$ with $N^\prime=1,2,\cdots$, no such trend is observed in the case of $N\neq 4N^\prime$. However, concrete conclusion requires extensive numerical analysis with large $N$, which is challenging.

Here:
- **Hamiltonians:** $H_{(N,K)}=\sum_iH_{(i,K)}$ is the stabilizer Hamiltonian of the circulant $K$-regular graph on $N$ sites, $H_{(i,K)}=[\bigotimes_{j\le K/2}Z_{i-j}]X_i[\bigotimes_{j\le K/2}Z_{i+j}]$.
- **Battery and charger:** the battery $H_B=H_{(N,K')}$ starts in a ground state $\rho(0)$, and the charger $H_C=H_{(N,K)}$ drives $\rho(t)=e^{-iH_Ct}\rho(0)e^{iH_Ct}$.
- **Work:** $W_{(N,K',K)}(t)=\mathrm{Tr}[(\rho(t)-\rho(0))H_B]$.

The definitions are quoted in [the literature note](../Library/QuantumContext/ghoshkonarfrancicapalsende2025stabilizer.md).

Issue [#20091](https://github.com/the-omega-institute/trureturing/issues/20091) fixes the reading: for every $N>2$ with $4\nmid N$ and all even interior degrees with $K'\ne K$, $L'\ne L$ and $|K-K'|=|L-L'|$, every pair of ground states gives $W_{(N,K',K)}(t)=W_{(N,L',L)}(t)$ for all $t\ge0$. Excluding the endpoint degrees $0$ and $K_{\max}$ makes the claim weaker than the literal one. It is refuted.

## Motivation

The paper compares stabilizer batteries and chargers of different graph degrees and looks for a quantum advantage in the stored work. The remark proposes that, away from multiples of four, the stored work depends on the two degrees only through their difference. That would reduce the two-parameter family of battery–charger pairs to one parameter.

## Gap

The literature check before any Lean is recorded in #20091:
- arXiv lists v2 as the latest version, and v2 keeps the remark;
- Semantic Scholar lists no citing works, and a web search found no follow-up;
- the search seat reports that the even-neighbourhood criterion of Wu–Kampermann–Bruß (2016) does not address the battery work, and that Zenodo and SSRN contain no settlement;
- the repository had no record.

`not-found-in-searched-scope`.

## Route

At $N=14$ ($K_{\max}=12$), take pair A $=(K',K)=(4,8)$ and pair B $=(2,6)$, both with difference $4$, and $t=\pi/4$.
1. **Ground state.** The graph-state vector $g(b)=2^{-N/2}(-1)^{\sum_ib_i+\sum_{\{i,j\}\in E}b_ib_j}$ satisfies $H_{(i,K')}g=-g$ for every $i$. Every $H_{(i,K')}$ is a Hermitian involution, so $g$ attains the lowest energy $-N$.
2. **Evolution.** The charger generators commute and square to the identity, so $e^{-iH_Ct}=\prod_j(\cos t-i\sin t\,H_{(j,K)})$.
3. **Quarter period.** At $t=\pi/4$, conjugation sends $H_{(i,K')}$ to $Q_i=H_{(i,K')}\prod_{j\in A_i}(-iH_{(j,K)})$, where $A_i$ is the set of charger generators that anticommute with it. So $W(\pi/4)=\sum_i(1+\mathrm{Re}\langle g,Q_ig\rangle)$.
4. **Expectations.** A Pauli string has nonzero expectation in the graph state only if its $Z$-part equals the adjacency matrix applied to its $X$-part.
   - For pair A every $Q_i$ is a stabilizer of the battery with eigenvalue $-1$, so $W_A(\pi/4)=0$.
   - For pair B no $Q_i$ passes the test, so $W_B(\pi/4)=14$.

Both facts are finite computations over $\mathbb F_2^{14}$, carried out in the module.

## Falsifier

The counterexample would not refute the remark if the module's work or ground states differed from the source's. The module:
- builds $H_{(N,K)}$ from the frozen Pauli words with the source's circulant graphs and periodic indices;
- defines a ground state as a unit vector of least energy, so the claim quantifies over every ground state, not only the graph state;
- defines the work literally from the matrix exponential and the rank-one initial density;
- requires interior degrees, so the endpoint cases cannot carry the failure.

## Evidence

The canonical source is `D5/S3/Quantum/Dynamics/StabilizerBatteryDegreeDifferenceRefutation.lean` (796 lines).
- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Dynamics/StabilizerBatteryDegreeDifferenceRefutation.lean.json`, statement `sha256:c52f01c94fff2cb9c619e43b75e0135dd6dc64f0fc997a67810bd66a796dd815`.

Declaration statements:
- `result`: `sha256:7f8e8ecef56c0755d00dbdeade63457bccaf359c003d07bbed85a74866b778dd`;
- `claim`: `sha256:21ede73713133283c7f9959ad243faf5171bca1923b9dff2f0cf38a59f1ced6c`.

## Triage

Tier 1 numerical observation of a 2025 paper (v2 2026), preregistered in issue #20091 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. `utility: kind=certified-instance; basis=refutes`. There is no digestion atom.

### What the settlement shows

**Proved in the module:** at $N=14$, the battery–charger pairs $(4,8)$ and $(2,6)$ have the same degree difference but store work $0$ and $14$ at $t=\pi/4$.

**Computed, not formalized** (orchestrator, exact state-vector simulation, recorded in #20091):
- the two works are $14$ and $10.5$ at $t=\pi/8$, and $6.644578605$ and $3.587292576$ at $t=0.19$, matching the closed forms $14(1-\cos^24t)$ and $14(1-\cos^42t)$;
- for interior degrees, no pair with equal difference differs for $N\le13$ with $4\nmid N$, so $N=14$ is the smallest interior counterexample;
- with the endpoint degrees allowed, $N=10$ already fails: $W_{(10,0,4)}\ne W_{(10,2,6)}$.

**Argued, not formalized.**
- *Mechanism.* The work is governed by which battery generators anticommute with which charger generators and by whether the conjugated generators fall back into the battery's stabilizer group. These overlaps depend on the two neighbourhoods themselves, not only on the difference of their radii. Wrapping around the cycle at $N=14$ makes the degree-$4$ and degree-$8$ neighbourhoods overlap in a way the degree-$2$ and degree-$6$ pair does not.
- *Family* (seat-reported, checked by the orchestrator at $N=14$ and $18$): the pairs $(2m-2,2m+2)$ and $(2,6)$ at $N=4m+2$ differ for every $m\ge3$, so the failure recurs for arbitrarily large $N$.
- *Effect on the paper.* The remark's dimension reduction to the single parameter $\Delta$ is unavailable; the stored work genuinely depends on both degrees.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
