---
slug: narasimhachar-gour-2015-cooling-map-thermal-operation-refutation
bibkey: narasimhachargour2015cooling
doi: 10.1038/ncomms8689
url: https://arxiv.org/abs/1409.7740v3
triage: theorem
motivation_gids:
  - D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.result
---

# A cooling-map transition has no finite ground-space thermal realization

## Problem

V. Narasimhachar and G. Gour, *Low-temperature thermodynamics with quantum coherence*, Nature Communications 6, 7689 (2015), arXiv:1409.7740v3, Supplementary subsection “Cooling maps and thermal operations”, Conjecture 1 (`LTT_arXiv.tex`, lines 924–927):

> Cooling maps are equivalent to low-temperature thermal operations, with regard to the feasibility of state transitions.

The next sentence distinguishes state-transition feasibility from equality of channel sets:

> Note that this could be true even if the set of cooling maps is strictly larger than that of thermal operations---there could still be a thermal operation achieving every state transition that is possible through cooling maps.

Issue [#26067](https://github.com/the-omega-institute/trureturing/issues/26067) fixes the following reading of the cooling-to-thermal direction. For every finite dimension $d$, every strictly increasing real energy spectrum $E$ with distinct positive gaps, and every pair of density matrices $\rho,\sigma$, a cooling-map transition $\rho\mapsto\sigma$ has a low-temperature thermal realization. Here:

- Density matrices are positive semidefinite complex matrices of trace one (`IsDensity`).
- A cooling map has a finite Kraus family, each member diagonal or of the form $c|j\rangle\langle k|$ with $j<k$, satisfying $\sum_a K_a^\dagger K_a=I$ and $\sum_a K_a\rho K_a^\dagger=\sigma$ (`IsCoolingKraus`, `IsCoolingMap`). This is the source's definition in `LTT_arXiv.tex`, lines 693–700.
- A thermal realization uses an arbitrary positive finite ancilla dimension $m$, arbitrary real ancilla energies $e$, and a unitary $U$ commuting with the diagonal total Hamiltonian $H_S\otimes I+I\otimes\operatorname{diag}(e)$ (`IsEnergyConserving`). If $G=\{a:e_a\le e_b\text{ for every }b\}$ and $g=|G|$, its output is $\operatorname{Tr}_A[U(\rho\otimes P_G/g)U^\dagger]$ (`groundSet`, `groundState`, `thermalOutput`). The full ground eigenspace, including every degeneracy, is retained.

The source writes the bath state as a low-temperature approximation to the normalized ground-space projector (lines 137–141 and 651–654). The formal assertion uses that projector exactly, as stipulated in #26067; it makes no assertion about an error tolerance or a positive-temperature Gibbs state. The resulting universal assertion is `claim`, and the module proves `result : ¬ claim`.

## Motivation

Narasimhachar and Gour (2015), arXiv:1409.7740v3, give a state-transition criterion for cooling maps, while thermal operations impose an operational requirement involving one energy-conserving unitary and a thermal ancilla. Conjecture 1 would make the tractable cooling-map criterion sufficient for exact thermal feasibility in the idealized low-temperature model. A state transition separating these models identifies a constraint that their cooling-map characterization does not capture.

## Gap

Issue #26067 records the bounded literature check:

- The search seat reports screening metadata for 295 citing records from OpenCitations and reading relevant passages of arXiv:1602.06969, 1607.00394, 1703.01826, 1708.04302, 1807.02942, 1807.11549, 2101.05690, 2205.13612, 2406.06234, 2410.14550 and 2510.05642, without finding a settlement of this conjecture as stated.
- The orchestrator reports two web searches without finding a proof or counterexample, and no existing repository dossier or preregistration for the conjecture.
- The checked v3 source explicitly states the conjecture and distinguishes it from equality of channels.

`not-found-in-searched-scope`. The citation screening and the readings of the citing works are reported evidence from #26067, not independently reproduced literature readings.

## Route

Use coordinates $0,1,2,3$. The following lemma names refer to the private helpers in the canonical module.

1. **A cooling transition.** Set $E=(0,1,3,7)$, $\rho=J_4/4$ with $J_4$ the all-ones matrix, and $\sigma=VV^\dagger/4$, where the rows of $V$ are $(1,0)$, $(0,1)$, $(3/5,4/5)$ and $(3/5,4i/5)$, where $i$ is the imaginary unit. Take the two diagonal Kraus operators whose diagonals are the columns of $V$. For these fixed data, `levels_valid` proves strict increase and distinct positive gaps, `kraus_complete` proves completeness, `sigma_diagonal` proves $\sigma_{jj}=1/4$ for every $j\in\mathrm{Fin}\,4$, `instance_density` proves that both matrices are density matrices, and `instance_cooling` proves the cooling transition. The input is the existing matrix `NiceErrorBasisNonNormalStabilizer.Pm`.
2. **Energy restriction and a nonempty ground space.** For any finite $m>0$ and real $e$, `ground_nonempty` proves $G\ne\varnothing$. For any finite system and ancilla dimensions, real spectra $E,e$, and complex matrix $U$ satisfying `IsEnergyConserving E e U`, `energy_entry` proves $U_{(j,b),(k,a)}=0$ whenever $E_j+e_b\ne E_k+e_a$. If additionally $E$ is strictly increasing, $a\in G$ and $k<j$, `energy_downward` proves that this entry vanishes.
3. **Population rigidity.** For the fixed four-level spectrum and input $\rho$, any finite $e$ and any complex $U$ commuting with the total Hamiltonian, `thermal_populations` expresses the real output population at $j$ as $(4g)^{-1}\sum_k\sum_{a\in G}\sum_b|U_{(j,b),(k,a)}|^2$. Suppose now that $m>0$, $U$ is unitary, energy conservation holds for the fixed spectrum, and the output equals the fixed $\sigma$. The matrix $T_{jk}=\sum_{a\in G}\sum_b|U_{(j,b),(k,a)}|^2$ has nonnegative entries, row sums $g$, column sums $g$, and $T_{jk}=0$ for $k<j$. For every real $4\times4$ matrix $T$ and real $g$ with exactly these four properties, `triangular_transport` proves $T_{jk}=0$ whenever $j\ne k$.
4. **Ground-space unitaries and their Gram matrix.** Under the same hypotheses $m>0$, arbitrary real $e$, unitary $U$, energy conservation for the fixed spectrum, and exact output $\sigma$ from $\rho$, `population_support` proves $U_{(j,b),(k,a)}=0$ whenever $a\in G$ and either $j\ne k$ or $b\notin G$. Given a unitary $U$ and this support condition, `block_unitary` proves that every restricted matrix $A_k=(U_{(k,b),(k,a)})_{b,a\in G}$ is unitary. Given this support condition and the exact output equality, `block_coherences` proves $\operatorname{tr}(A_iA_j^\dagger)=g(VV^\dagger)_{ij}$ for every $i,j\in\mathrm{Fin}\,4$.
5. **Incompatible linear relations.** For any finite index type $n$ and any four matrices $A_k\in M_n(\mathbb C)$ satisfying $\operatorname{tr}(A_iA_j^\dagger)=|n|(VV^\dagger)_{ij}$ for every $i,j$, `gram_null` proves $A_2=(3/5)A_0+(4/5)A_1$ and $A_3=(3/5)A_0+(4i/5)A_1$. For a nonempty finite index type with decidable equality, four unitary matrices satisfying both relations contradict `unitary_obstruction`: expanding the two unitary identities gives $X+X^\dagger=0$ and $X-X^\dagger=0$ for $X=A_0A_1^\dagger$, hence $X=0$, whereas a product of unitaries on a nonempty space is invertible and nonzero.
6. **Negation of the universal claim.** `thermal_impossible` combines these facts: for every $m>0$, every real $e$, and every unitary $U$ conserving total energy for the fixed four-level spectrum, equality of its thermal output from $\rho$ with the fixed $\sigma$ implies `False`. Applying `claim` to the certified cooling transition would supply exactly such data, which proves `result`.

## Falsifier

The refutation would not settle the preregistered assertion if it excluded only a particular Kraus implementation, fixed the ancilla dimension or ground multiplicity, omitted the density conditions, or permitted a degenerate system spectrum. The module checks the fixed input and output as density matrices, certifies the system spectrum, and excludes every positive finite ancilla, every real ancilla spectrum and every energy-conserving unitary producing that output. The witness uses two diagonal Kraus operators and no nonzero lowering operators, meeting the source's Kraus restrictions. The thermal model allows arbitrary ground degeneracy and uses the normalized projector onto the entire ground space; `ground_nonempty` supplies the nonzero normalization for $m>0$.

The conclusion concerns exact finite ground-space thermal operations. Infinite-dimensional ancillas, approximation by thermal outputs, positive-temperature baths, catalysts and external coherence resources require separate statements.

## Evidence

The canonical source is `D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:d6c1048ed19e978a5a6b5e895428c792b2890a9f35ad4281bd7711714bb3184a`;
- `claim`: `sha256:915823fb300a47273b3b33f468beeac46d9e99302d5a3f05f0d0606ff17c86a4`.

## Triage

Tier 1 conjecture of a 2015 Nature Communications paper, preregistered in issue #26067 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that, for every finite dimension and every strictly increasing spectrum with distinct positive gaps, every cooling-map transition between density matrices has an exact realization using a positive finite-dimensional ancilla in its normalized full ground-space state and a unitary commuting with total energy.

**Computed, not formalized:** None.

**Argued, not formalized.**

- *Missing structure.* Cooling-map feasibility supplies compatible Kraus vectors, whereas a thermal realization must obtain all coherences from one common energy-conserving unitary. For the fixed $E,\rho,\sigma$, the hypotheses of `thermal_impossible` are $m>0$, arbitrary real ancilla energies, a unitary $U$, commutation with total energy, and exact output $\sigma$ from $\rho$. Under these hypotheses, the `population_support`, `block_coherences`, `gram_null` and `unitary_obstruction` steps in Route isolate the additional compatibility constraint: the prescribed vector Gram matrix would have to be a normalized trace Gram matrix of unitaries on one nonempty ground space. Positive semidefiniteness of the vector Gram matrix does not supply that structure.
- *A sufficient repair.* For a diagonal cooling channel $\Phi_C(\rho)_{ij}=C_{ij}\rho_{ij}$, suppose there are a positive integer $g$ and $g\times g$ unitaries $A_i$ with $C_{ij}=\operatorname{tr}(A_iA_j^\dagger)/g$. Choose an ancilla with $g$ coordinates, all energies zero, and set $U=\sum_i|i\rangle\langle i|\otimes A_i$. This matrix is unitary and commutes with the system Hamiltonian tensored with the identity. Tracing out its maximally mixed ancilla gives $\Phi_C$ entry by entry, establishing a sufficient realization condition. In particular, if $C=zz^\dagger$ and $|z_i|=1$ for every $i$, a one-dimensional ancilla and the diagonal system unitary $\operatorname{diag}(z)$ suffice.
- *Ancilla energy basis.* For any finite Hermitian ancilla Hamiltonian, a unitary basis change $W$ diagonalizes it and carries its full ground projector to the coordinate projector used here. Replacing $U$ by $(I\otimes W^\dagger)U(I\otimes W)$ preserves total-energy commutation in the new basis. Invariance of the partial trace under ancilla basis changes preserves the system output. This justifies the diagonal-ancilla reading; the basis-change argument is not separately formalized in this module.
- *Nearby source statements.* Narasimhachar and Gour (2015), arXiv:1409.7740v3, separately state “Cooling maps are equivalent to low-temperature thermal operations on two-level systems.” (`LTT_arXiv.tex`, line 963) and “All optimally coherent processes are low-temperature thermal operations.” (line 993). The four-level refutation does not negate these restricted statements, and this module does not formalize them. Their supplementary mixture corollary states “Any mixture of optimally coherent processes can be approximated arbitrarily well by a thermal operation.” (line 1022); its proof treats rational convex combinations exactly and uses density for arbitrary mixtures (lines 1025–1041). That approximation statement is outside the exact-realization settlement.
- *Effect on the paper.* The main cooling-map state-transition theorem assumes every matrix entry of $\rho$ is nonzero and requires upper-triangular majorization of the populations together with positivity of its matrix $Q$ (lines 176–185). For the displayed pair the populations coincide and $Q=VV^\dagger$, so these conditions are satisfied. They therefore cannot be promoted, using Conjecture 1, to sufficient conditions for exact finite ground-space thermal transitions. The conjectural coincidence of state-transition sets depicted in the source's inclusion hierarchy is ruled out under the preregistered reading. The cooling-map characterization itself, the separately stated restricted thermal constructions and the Gibbs-preserving results do not acquire a refutation merely from this counterexample.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The OpenCitations count, metadata screening, readings of the eleven citing works, web-search results and repository search reported in #26067 were not independently reproduced. The source quotations and their locations were checked against `LTT_arXiv.tex` from arXiv:1409.7740v3.

The search seat's reported symbolic checks, rational family, extension to higher dimensions and robustness estimate were not independently reproduced and are not used as settlement evidence.

The sufficient repair, rank-one construction, ancilla basis-change bridge and consequences for other source statements in “Argued, not formalized” are mathematical arguments rather than additional compiled declarations. The source's restricted thermal constructions and approximation corollary are source readings, not Lean results of this module. No claim is made here about positive-temperature or approximate thermal reachability, infinite-dimensional baths, catalytic or coherence-assisted variants, or equivalence restricted to three-level systems.
