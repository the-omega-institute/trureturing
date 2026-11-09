---
slug: cheng-milne-hall-wiseman-2016-four-qubit-correlation-monogamy
bibkey: chengmilnehallwiseman2016volume
doi: 10.1103/PhysRevA.94.042105
url: https://arxiv.org/abs/1606.02390v2
triage: theorem
motivation_gids:
  - D5/S3/QuantumStates/FourQubitCorrelationMonogamy.result
---

# Four-qubit pair-correlation monogamy

## Problem

S. Cheng, A. Milne, M. J. W. Hall and H. M. Wiseman, *Volume monogamy of quantum steering ellipsoids for multi-qubit systems*, Phys. Rev. A 94, 042105 (2016), arXiv:1606.02390v2, Sec. III C, p. 6, Eq. (36) (`finalversion.tex`, lines 395–399):

> Finally, we conjecture that inequality (35) generalises to
>
> $\operatorname{Tr}[T_{AB}T_{AB}^{\top}]+\operatorname{Tr}[T_{AC}T_{AC}^{\top}]+\operatorname{Tr}[T_{AD}T_{AD}^{\top}]\leq 3.$
>
> for all pure 4-qubit states.

The source defines $T_{jk}=\operatorname{Tr}[\rho_{AB}\sigma_j\otimes\sigma_k]$ for $j,k=1,2,3$ in Sec. II, Eq. (2) (`finalversion.tex`, lines 129–133). Thus each term in Eq. (36) is the sum of the nine squared real entries of a two-qubit correlation matrix.

Issue [#26136](https://github.com/the-omega-institute/trureturing/issues/26136) fixes the reading. In the module, a vector $\psi:(\mathrm{Fin}\,4\to\mathrm{Fin}\,2)\to\mathbb C$ has its sixteen computational-basis amplitudes indexed by four bits. The qubits are ordered $A,B,C,D$. The indices $X=0,1,2$ denote targets $B,C,D$, and $i,j=0,1,2$ denote Pauli directions $x,y,z$. Let $P_{Xij}$ be `wordOp (twoBodyWord X i j)`: Pauli $i$ on $A$, Pauli $j$ on target $X$, and identities elsewhere. The definition `rankOneDensity` is the outer product $\psi\psi^{\dagger}$, and `correlation` is

$$c_{Xij}(\psi)=\operatorname{Re}\operatorname{Tr}[\psi\psi^{\dagger}P_{Xij}].$$

The proposition `claim` states, exactly,

$$\forall\psi,\quad \sum_q\overline{\psi(q)}\psi(q)=1\quad\Longrightarrow\quad
\sum_{X=0}^{2}\sum_{i=0}^{2}\sum_{j=0}^{2}c_{Xij}(\psi)^2\leq3.$$

The module proves `result : claim`. The correspondence with reduced-state correlation matrices is explained below.

## Motivation

The conjecture constrains how strongly one qubit can correlate with three other qubits through their two-body spin observables. Cheng–Milne–Hall–Wiseman (2016), Sec. III C, obtains the bound for locally filtered canonical pure states in Eq. (35), and asks in Eq. (36) whether it holds for every pure four-qubit state. The source also identifies this conjecture as a sufficient input for extending its four-qubit steering-volume monogamy relation, Eq. (28), to mixed states.

## Gap

The bounded literature check recorded in #26136 reports:

- the explicit conjecture remains in arXiv:1606.02390v2;
- the citation search reported there covered the latest sources of 39 arXiv-linked works among 50 INSPIRE citing records, including arXiv:1909.13152, 2003.10626, 2301.01714, 2312.06369, 2404.02725 and 2607.00346, without finding an unrestricted settlement of Eq. (36);
- the orchestrator's searches found no settlement, and distinguished the general anticommuting-observable bound in Kurzyński–Paterek–Ramanathan–Laskowski–Kaszlikowski, *Correlation complementarity yields Bell monogamy relations* (2011), arXiv:1010.2012, from this particular correlation-matrix inequality;
- the preregistration records no existing repository dossier on this conjecture.

`not-found-in-searched-scope`.

## Route

All helper names in this section belong to `FourQubitCorrelationMonogamy` unless qualified otherwise.

1. **Three families.** For every $k\in\mathrm{Fin}\,3$ and $u=(X,j)\in\mathrm{Fin}\,3\times\mathrm{Fin}\,3$, put $P^k_u=P_{X,k+X,j}$, where addition is modulo three. For $u\ne v$, `partition_sign` proves that the product of their four single-site commutation signs is $-1$. For each $k$, `group_relations` proves that all nine matrices are Hermitian, each squares to the identity, and any two with unequal indices anticommute. If the targets agree, unequal indices force different target Pauli letters; if the targets differ, the Pauli letters on $A$ differ. Exactly one site contributes anticommutation in either case.
2. **One family costs at most one.** The lemma `anticommuting_family_bound` assumes a finite matrix index type $n$ with decidable equality, a finite family index type $\alpha$, a density state $\rho$ on $n$ (a positive semidefinite complex matrix of trace one), and matrices $P_\ell$ that are Hermitian, satisfy $P_\ell^2=I$, and satisfy $P_\ell P_m=-P_mP_\ell$ whenever $\ell\ne m$. With $a_\ell=\operatorname{Re}\operatorname{Tr}(\rho P_\ell)$, $s=\sum_\ell a_\ell^2$ and $H=\sum_\ell a_\ell P_\ell$, the involution and anticommutation hypotheses give $H^2=sI$. Hermiticity of the $P_\ell$ and real coefficients make $H$ Hermitian. Trace linearity and trace-one normalization give $\langle H\rangle_\rho=s$ and $\langle H^2\rangle_\rho=s$. The imported `CovarianceSumBound.variance_nonneg`, for a density state and a Hermitian observable, gives $0\leq s-s^2$, hence $s\leq1$.
3. **Reindex and sum.** For every density state $\rho$ on $\mathrm{Fin}\,4\to\mathrm{Fin}\,2$ and every $k\in\mathrm{Fin}\,3$, `group_bound` bounds $\sum_{X,j}\langle P_{X,k+X,j}\rangle_\rho^2$ by one. For every real-valued function $f$ of three $\mathrm{Fin}\,3$ indices, `partition_sum` reindexes $\sum_{X,i,j}f(X,i,j)$ as $\sum_{k,X,j}f(X,k+X,j)$ using the bijection $k\mapsto k+X$. Consequently `density_bound` proves the correlation sum is at most three for every such density state, including mixed states.
4. **Normalized vectors.** For every $\psi$ satisfying $\operatorname{star}\psi\mathbin{\boldsymbol\cdot}\psi=1$, `EnergyEigenstateStationarity.pureDensityState` packages $\psi\psi^{\dagger}$ as a positive trace-one density state. Under precisely this normalization hypothesis, `pure_specialization` applies `density_bound` and identifies its expectations with `correlation`; `result` proves `claim`.

## Falsifier

A normalized four-qubit vector whose defined correlation sum exceeded three would contradict `result`. A discrepancy between these correlations and the source's reduced-state entries would instead invalidate the interpretation as a settlement of Eq. (36).

The definitions fix the relevant checks: `twoBodyWord` uses position zero for $A$, `X.succ` for the target, and identity letters at the other positions; `wordOp` is the entrywise-defined tensor product of the standard Pauli matrices, with $Y=iXZ$; `rankOneDensity` is $\psi\psi^{\dagger}$; and `correlation` takes the real trace expectation. There is no optimization quantity or infimum whose nonemptiness or boundedness must be supplied. The partial-trace interpretation is an ordinary finite-index argument, not a separately stated theorem in this module.

## Evidence

The canonical source is `D5/S3/QuantumStates/FourQubitCorrelationMonogamy.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/QuantumStates/FourQubitCorrelationMonogamy.lean.json`.

Declaration statements:

- `result`: `sha256:2e7bdc8d42d8a867581ca0a945fda8600c3e2009c40c2f4b42279f9ccbb5c0f0`;
- `claim`: `sha256:37969259592a823ccf9ba34e3084f2421dc566c7843db1d433d44a50d253e6d8`.

## Triage

Tier 1 conjecture of a 2016 paper, preregistered in issue #26136 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every complex four-qubit amplitude vector $\psi$ with $\sum_q\overline{\psi(q)}\psi(q)=1$, the sum of the twenty-seven squares $c_{Xij}(\psi)^2$, for $X,i,j\in\mathrm{Fin}\,3$, is at most three, where $c_{Xij}$ is the real trace expectation defined above.

**Computed, not formalized:** None.

**Argued, not formalized.**

- *Decisive mechanism.* For each $k\in\mathrm{Fin}\,3$, the nine Pauli words of `group_relations` turn the three incompatible Pauli directions on $A$ into one pairwise-anticommuting family across the three targets. For a finite matrix index type with decidable equality, a finite family of Hermitian involutions, and a positive trace-one state on that matrix index type, with the involutions anticommuting at distinct family indices, the cancellation in `anticommuting_family_bound` leaves only the squared coefficient sum in $H^2$. This explains why no marginal-purity identity is required; the formal density-state version is `density_bound` with the hypotheses given in Route.
- *Correspondence with the source.* Order the computational-basis indices as $(a,x,r)$, with $r$ the two remaining qubits. For any four-qubit density matrix $\rho$, the reduced matrix has entries $(\rho_{AX})_{ax,a'x'}=\sum_r\rho_{axr,a'x'r}$. Expanding the trace against $\sigma_i\otimes\sigma_j\otimes I$ gives $\sum_{a,x,a',x',r}\rho_{axr,a'x'r}(\sigma_i)_{a'a}(\sigma_j)_{x'x}$, which is exactly $\operatorname{Tr}(\rho_{AX}\sigma_i\otimes\sigma_j)$. For Hermitian $\rho$ and $P$, conjugation and trace cyclicity give $\overline{\operatorname{Tr}(\rho P)}=\operatorname{Tr}(P\rho)=\operatorname{Tr}(\rho P)$, so taking the real part changes nothing. Finally $\operatorname{Tr}(TT^{\top})=\sum_{i,j}T_{ij}^2$ for a real correlation matrix. These identities give the intended reading of `claim` as Eq. (36).
- *Sharpness and neighbouring systems.* In $|0000\rangle$, each $ZZ$ correlation between $A$ and a target equals one, while every correlation involving $X$ or $Y$ has a zero one-qubit expectation and vanishes. Thus three cannot be replaced by a smaller uniform constant. For the analogous star of $r>3$ target qubits, $|0\rangle^{\otimes(r+1)}$ instead has correlation sum $r$, so the same constant three cannot extend to those systems. A classification of all four-qubit equality states and optimal bounds for larger systems is not supplied by `result`.
- *Effect on the paper.* Cheng–Milne–Hall–Wiseman (2016), p. 6, immediately after Eq. (36), states: “The validity of this conjecture would imply, using the same techniques as above, that monogamy relation (28) in fact holds for all 4-qubit states.” The implication can be justified for any four-qubit density state $\rho$ as follows. If $\rho_A$ has full rank, filtering by $F=(2\rho_A)^{-1/2}$ on $A$ gives a positive state $\widetilde\rho$ of trace $\operatorname{Tr}(F^2\rho_A)=1$, with $\widetilde\rho_A=I/2$. Invertibility makes $E\mapsto FEF$ a bijection on positive measurement effects up to rescaling; rescaling leaves a conditional state unchanged, so the steering ellipsoids and their normalized volumes are unchanged. In this canonical state the source's Eq. (8) gives $v_{X|A}=|\det\widetilde T_{AX}|$. Applying the arithmetic-geometric mean inequality to the three nonnegative eigenvalues of $\widetilde T_{AX}\widetilde T_{AX}^{\top}$ gives $v_{X|A}^{2/3}\leq\operatorname{Tr}(\widetilde T_{AX}\widetilde T_{AX}^{\top})/3$. Summing and applying `density_bound` to the positive trace-one four-qubit state $\widetilde\rho$ gives $\sum_X v_{X|A}^{2/3}\leq1$, the mixed-state form of Eq. (28). If $\rho_A$ is pure, positivity forces support on its one-dimensional $A$ factor, so the state factorizes across $A|BCD$ and every steering ellipsoid has zero volume. This removes the conjectural input to the source's mixed-state implication; the steering-volume quantities, filtering argument and determinant comparison are not formalized in the module. The source's further questions about stronger volume bounds and higher-dimensional systems remain outside this settlement.

## ASSUMED-UNVERIFIED

The literature check is bounded and does not establish exhaustive worldwide novelty or priority. The 50-record citation count, the search of 39 arXiv-linked works, the later-paper readings and the negative search results are attributed to #26136 and were not independently reproduced. In particular, the readings of arXiv:1909.13152, 2003.10626 and 1010.2012 are reported by that issue, not verified here.

All arguments labelled “Argued, not formalized” are outside the proposition proved by `result`. In particular, the partial-trace correspondence, sharpness, larger-system product-state comparison and mixed-state steering-volume consequence are not separate formal statements in this module. Equality-case classification and optimal bounds beyond four qubits are not settled here.
