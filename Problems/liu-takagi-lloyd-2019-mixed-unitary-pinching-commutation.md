---
slug: liu-takagi-lloyd-2019-mixed-unitary-pinching-commutation
bibkey: liutakagilloyd2019diagonaldiscord
doi: 10.1088/1751-8121/ab0774
url: https://arxiv.org/abs/1708.09076v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/MixedUnitaryPinchingCommutation.result
---

# Non-isotropic mixed-unitary qubit channels do not commute with marginal pinching

## Problem

Z.-W. Liu, R. Takagi and S. Lloyd, *Diagonal quantum discord*, J. Phys. A: Math. Theor. 52, 135301 (2019), arXiv:1708.09076v2, Section 3.2, “$\pi$-commuting local operations and monotonicity”, conjecture following the probabilistic-Hadamard example:

> We conjecture (which is not important for our current purpose) that ${\bf ISO} = X_A(\pi_A)$. That is, qubit mixed-unitary channels that are not isotropic all fail to satisfy the condition.

This quotation is line 463 of the source archive's `revised_jphysa_clean.tex` (md5 `3ae0def434187ebe1875d87961e23048`). The relevant definitions are at lines 261, 325–329 and 347; line 339 assumes the input marginal nondegenerate. See also [the literature note](../Library/Entropy/liutakagilloyd2019diagonaldiscord.md).

The formal definitions use the following conventions:

- `IsMixedUnitary` means a finite mixture $\Phi(a)=\sum_j p_j U_j a U_j^\dagger$ on every complex $2\times2$ matrix, with real $p_j\ge0$, $\sum_jp_j=1$, and unitary $U_j$.
- `IsIsotropic` means that, for some fixed $\gamma\in[0,1]$ and unitary $U$, either $\Phi(a)=(1-\gamma)UaU^\dagger+\gamma\operatorname{tr}(a)I/2$ for every $a$, or $\Phi(a)=(1-\gamma)Ua^{\mathsf T}U^\dagger+\gamma\operatorname{tr}(a)I/2$ for every $a$. Transpose gives the complex linear extension of the antiunitary action on Hermitian states.
- `localMap` applies $\Phi$ to each first-qubit block; for these linear maps it is $\Phi\otimes\mathrm{id}_B$. The marginal $\rho_A=\operatorname{tr}_B\rho$ is `partialTraceRight`.
- `IsNondegenerate` means Hermitian with two distinct eigenvalues. For a Hermitian marginal, `pinchA` is $\pi_A(\rho)=\sum_i(P_i\otimes I)\rho(P_i\otimes I)$, where $P_i$ are its rank-one spectral projectors; its spectral basis is recomputed on the argument to which pinching is applied.

Issue [#22787](https://github.com/the-omega-institute/trureturing/issues/22787) fixes the reading to the quotation's second sentence: for every mixed-unitary qubit map $\Phi$ that is not isotropic, there is a positive semidefinite two-qubit matrix $\rho$ of trace one such that $\rho_A$ and $\Phi(\rho_A)$ are nondegenerate and $\pi_A((\Phi\otimes\mathrm{id}_B)(\rho))\ne(\Phi\otimes\mathrm{id}_B)(\pi_A(\rho))$. This is proved.

## Motivation

The source uses commutation with the discord-destroying map as a sufficient condition for monotonicity of relative-entropy diagonal discord. Classifying the mixed-unitary channels satisfying that condition identifies the reach of this monotonicity argument. Failure to commute does not by itself assert an increase of diagonal discord.

## Gap

The literature check before any Lean is recorded in #22787:

- the conjecture occurs in the 2019 arXiv v2 source;
- the oracle-reported searches of Zenodo, ResearchGate, SSRN and GitHub by title and conjecture wording found no settlement;
- the oracle-reported readings of Sone et al., Phys. Rev. A 98, 012115 (2018), and Phys. Rev. A 99, 052318 (2019), found no settlement of this classification;
- the orchestrator's searches of repository issues and of `Problems/`, `Library/` and `D5/` found no prior record of the problem.

`not-found-in-searched-scope`.

## Route

Write $S(v)=v\cdot\sigma$ for the real Pauli combination, $T$ for `blochOperator`, and $Q=T^{\mathsf T}T$.

1. **Bloch representation.** For a qubit map satisfying `IsMixedUnitary`, `mixed_channel_data` supplies a complex linear representative, preservation of the identity, trace and Hermiticity, and $\Phi(S(v))=S(Tv)$ for every real $v\in\mathbb R^3$. Here $T_{ij}=\operatorname{Re}\operatorname{tr}(\sigma_{i+1}\Phi(\sigma_{j+1}))/2$.
2. **Scalar Gram matrices.** For a mixed-unitary $\Phi$ and real $c$ with $T^{\mathsf T}T=cI$, `scalar_gram_bounds` gives $0\le c\le1$. For any real $3\times3$ matrix $O$ with $O^{\mathsf T}O=I$, `orthogonal_spin_lift` implements its action on all Pauli combinations by either unitary conjugation or unitary conjugation after transpose. Thus `scalar_gram_isotropic`, assuming `IsMixedUnitary` and the existence of such a real $c$, gives `IsIsotropic`: $c=0$ gives complete depolarization, while $c>0$ uses $T=\sqrt c\,O$ and $\gamma=1-\sqrt c$. Non-isotropy therefore excludes a scalar Gram matrix.
3. **Orthogonal probes.** For any real $3\times3$ matrix $T$ for which no real $c$ satisfies $T^{\mathsf T}T=cI$, `orthogonal_probe` supplies real $n,x$ with $n\cdot n=x\cdot x=1$, $n\cdot x=0$ and $(Tn)\cdot(Tx)\ne0$. A nonzero off-diagonal entry of $Q$ supplies coordinate directions; otherwise unequal diagonal entries supply their sum and difference. `normalize_probe` applies to real $a,b$ with $a\cdot b=0$ and $(Ta)\cdot(Tb)\ne0$, and normalizes them without losing either condition.
4. **A density matrix and its image.** Set $R(n,x)=\tfrac14[I\otimes I+\tfrac12S(n)\otimes I+\tfrac14S(x)\otimes Z]$, the definition `witness`. Under $n\cdot n=x\cdot x=1$ and $n\cdot x=0$, `witness_density` proves positive semidefiniteness and trace one. For arbitrary real $n,x$, `witness_marginal` gives $\operatorname{tr}_B R(n,x)=(I+S(n)/2)/2$. For mixed-unitary $\Phi$ and arbitrary real $n,x$, `local_witness` gives $(\Phi\otimes\mathrm{id}_B)R(n,x)=R(Tn,Tx)$, and `mapped_marginal` identifies its marginal with $\Phi(\operatorname{tr}_B R(n,x))=(I+S(Tn)/2)/2$.
5. **Spectral pinching.** For any complex two-qubit matrix $\tau$ whose first marginal is $(I+S(v))/2$ with real $v\ne0$, `pinching_formula` gives $\pi_A(\tau)=\tfrac12[\tau+(v\cdot v)^{-1}(S(v)\otimes I)\tau(S(v)\otimes I)]$. Consequently `pinch_witness`, for arbitrary real $a,b$ with $a\ne0$, gives $\pi_A(R(a,b))=R(a,[(a\cdot b)/(a\cdot a)]a)$. For real $v\ne0$, `bloch_nondegenerate` proves that $(I+S(v))/2$ is nondegenerate; applying it to $n/2$ and $Tn/2$ supplies the two required nondegeneracy conclusions.
6. **Nonzero commutator.** For mixed-unitary $\Phi$, real $n,x$ with $n\cdot n=1$, $n\cdot x=0$, and $Tn\ne0$, `commutator_identity` gives $\pi_A((\Phi\otimes\mathrm{id}_B)R(n,x))-(\Phi\otimes\mathrm{id}_B)(\pi_A(R(n,x)))=\frac{(Tn)\cdot(Tx)}{16\,(Tn)\cdot(Tn)}S(Tn)\otimes Z$. For any real $a,b$ with $a\cdot b\ne0$, `commutator_nonzero` proves that the corresponding expression $\frac{a\cdot b}{16\,a\cdot a}S(a)\otimes Z$ is nonzero. The probes satisfy these hypotheses, yielding `result`.

## Falsifier

The settlement would miss the registered problem if the channel class, marginal or pinching differed from the source's. The definitions use actual finite unitary mixtures, both isotropic forms, the partial trace over the second qubit, and the first marginal's spectral projectors. The antiunitary alternative is not omitted.

`pinchA` chooses a spectral basis even at a degenerate Hermitian marginal and returns its argument outside the Hermitian-marginal domain. `result` avoids these extensions: both $\rho_A$ and $\Phi(\rho_A)$ are nondegenerate, and `mapped_marginal`, for mixed-unitary $\Phi$ and arbitrary real $n,x$, identifies the latter with the actual output marginal of $R(n,x)$. The probes have $(Tn)\cdot(Tx)\ne0$, which forces $Tn\ne0$, so the commutator formula uses no inverse at zero. The zero Bloch matrix belongs to the scalar-Gram, isotropic case. Invertibility of $T$ is not assumed.

## Evidence

The canonical source is `D5/S3/Quantum/Information/MixedUnitaryPinchingCommutation.lean`.

- **Proof.** It proves `result` with the universally quantified existence statement in Problem.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/MixedUnitaryPinchingCommutation.lean.json`.

Declaration statements:

- `result`: `sha256:99836e9c6706852219dcffb2afe124e67e66365bba871d411be5c464e596b7ae`.

## Triage

Tier 1 conjecture of a 2019 journal paper, preregistered in issue #22787 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every map on complex qubit matrices satisfying `IsMixedUnitary` and not `IsIsotropic`, there exists a positive semidefinite two-qubit matrix of trace one whose first marginal and its image under the map are both nondegenerate, and on which marginal pinching and the local map do not commute.

**Computed, not formalized:** the random mixed-unitary channels and random states that the orchestrator recorded in #22787 agree with the formal statement: each constructed witness for a non-isotropic channel gave a nonzero commutator, and no violation was observed for the tested isotropic channel.

**Argued, not formalized.**

- *Decisive mechanism and singular maps.* For mixed-unitary $\Phi$ and unit orthogonal $n,x$ with $(Tn)\cdot(Tx)\ne0$, `local_witness` maps $R(n,x)$ to $R(Tn,Tx)$; `pinch_witness`, applicable to any real $a\ne0$ and $b$, retains only the component of $b$ parallel to $a$. Thus the correlation along $x$ is erased at the input, while its transformed component parallel to $Tn$ survives output pinching. The nonzero inner product guarantees $Tn\ne0$ even when $T$ is singular. This mechanism uses no lower bound on a singular value; `result` supplies no quantitative lower bound on the commutator.
- *Entanglement is unnecessary for this construction.* For unit orthogonal $n,x$, write $\tau_\pm=[I+S(n)/2\pm S(x)/4]/2$. Their Bloch vectors have length $\sqrt5/4<1$, so they are qubit density matrices, and $R(n,x)=\tfrac12\tau_+\otimes|0\rangle\langle0|+\tfrac12\tau_-\otimes|1\rangle\langle1|$ is separable. Each $\tau_\pm$ has eigenvalues $(4\pm\sqrt5)/8$, so $R(n,x)$ has the positive eigenvalues $(4+\sqrt5)/16$ and $(4-\sqrt5)/16$, each twice. These separability and exact-spectrum statements are additional arguments, not conclusions stated by `result`.
- *Why the mixed-unitary restriction matters.* Fix a nondegenerate qubit density $\sigma=\sum_i p_i|i\rangle\langle i|\ne I/2$ and let $\Phi_\sigma(a)=\operatorname{tr}(a)\sigma$. The Kraus operators $\sqrt{p_i}|i\rangle\langle j|$, for $i,j\in\{0,1\}$, give this channel and satisfy $\sum_{i,j}K_{ij}^\dagger K_{ij}=I$. Its local output is $\sigma\otimes\rho_B$, fixed by pinching in the eigenbasis of $\sigma$. Input pinching preserves $\rho_B$, since the input spectral projectors sum to the identity, so both orders give $\sigma\otimes\rho_B$ for every bipartite density with nondegenerate input marginal. But $\Phi_\sigma(I)=2\sigma\ne I$, whereas every mixed-unitary or isotropic map defined above is unital. This supplies commuting channels outside those classes and shows why the quotation's unrestricted set equality needs qualification. The formal settlement is its mixed-unitary sentence.
- *Effect on the paper and neighbouring questions.* The source's isotropic inclusion (TeX line 412) and its qubit monotonicity corollary for $\mathbf{SC}\cup\mathbf{ISO}$ (line 454) do not depend on the conjecture at line 463. On the nondegenerate input-and-output domain, the settlement supplies the complementary exclusion of every non-isotropic mixed-unitary channel; the source's converse is not formalized here. Its separate Conjecture 1 (line 470), “For $d_A= 2$, diagonal discord is monotonically nonincreasing under any local discord nongenerating channel.”, remains open in this settlement: noncommutation removes a sufficient monotonicity argument, but gives no entropy comparison. No higher-dimensional classification or universal treatment of degenerate marginals is supplied by `result`.

## ASSUMED-UNVERIFIED

The literature check is bounded and does not establish exhaustive worldwide novelty or priority. The v2 TeX source and its conjecture were independently read; the preregistration's arXiv revision metadata, Crossref reading, AQIS 2017 slides claim, prior-settlement web searches, and readings of Sone et al., Phys. Rev. A 98, 012115 (2018), and Phys. Rev. A 99, 052318 (2019), were not independently reproduced.

The numerical checks are the orchestrator's readings in #22787 and were not rerun. All statements labelled “Computed, not formalized” or “Argued, not formalized”, including separability, the exact witness spectrum, the replacement-channel example and the implications for the paper, are outside the statement of `result`. The published isotropic converse and monotonicity results remain external literature results; the separate monotonicity conjecture, higher-dimensional extensions and degenerate-marginal classification are not settled here.
