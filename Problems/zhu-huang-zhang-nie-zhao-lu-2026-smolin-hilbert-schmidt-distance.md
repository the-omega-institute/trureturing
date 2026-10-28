---
slug: zhu-huang-zhang-nie-zhao-lu-2026-smolin-hilbert-schmidt-distance
bibkey: zhuhuangzhangniezhaolu2026universal
doi: 10.1103/82gn-78lv
url: https://arxiv.org/abs/2610.17592v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance.result
---

# Exact Hilbert–Schmidt distances for noisy four-qubit Smolin states

## Problem

X. Zhu, K. Huang, C. Zhang, X. Nie, Q. Zhao and D. Lu, *Universal entanglement detection with geometrically optimal witnesses*, arXiv:2610.17592v1 [quant-ph]; Phys. Rev. A 114, 042409 (2026), Appendix, “Four-qubit Smolin state”. The source TeX is `manuscript.tex` (1053 lines, MD5 `db9c376c24127cc118b3e270cf74af42`). Lines 672–687 state:

> A natural conjecture is that
>
> $D(\mathcal{N}_p(\rho_S)) = \begin{cases} 0, & p \in [0, \frac{1}{3}], \\ \|\mathcal{N}_p(\rho_S) - \mathcal{N}_{\frac{1}{3}}(\rho_S)\|, & p \in (\frac{1}{3}, 1], \end{cases}$
>
> which simplifies to
>
> $D(\mathcal{N}_p(\rho_S)) = \begin{cases} 0, & p \in [0, \frac{1}{3}], \\ \frac{\sqrt{3}}{4} \left( p - \frac{1}{3} \right), & p \in (\frac{1}{3}, 1]. \end{cases}$

Here the norm is Hilbert–Schmidt, $\|X\|_{\mathrm{HS}}=\sqrt{\operatorname{Re}\operatorname{tr}(X^\dagger X)}$. The appendix defines $\rho_S=(I+\sigma_x^{\otimes4}+\sigma_y^{\otimes4}+\sigma_z^{\otimes4})/16$ at lines 659–661, $D(\rho)=\min_{\sigma\in\mathrm{SEP}(\mathcal P)}\|\rho-\sigma\|$ at lines 662–665, and $\mathcal N_p(\rho_S)=p\rho_S+(1-p)I/16$ at lines 669–671. Its four representative partitions are $\{1\}:\{2,3,4\}$, $\{1\}:\{2\}:\{3,4\}$, $\{1\}:\{2\}:\{3\}:\{4\}$ and $\{1,2\}:\{3,4\}$ (line 666).

Issue [#20844](https://github.com/the-omega-institute/trureturing/issues/20844) fixes the reading: for every $p\in[0,1]$, the distance is the displayed function $f(p)$ for the first three partitions, and zero for the two-pair partition, which the source identifies as separable at line 668. Every minimum is attained. This is proved. The source and definitions are also recorded in [the literature note](../Library/QuantumContext/zhuhuangzhangniezhaolu2026universal.md).

## Motivation

The source constructs geometrically optimal entanglement witnesses from exact nearest separable states (lines 101–112). Its numerical optimization supplies approximate candidates without a global-minimum certificate (lines 134–136). The Smolin conjecture asks for an exact distance and a nearest state along a whole white-noise family. An attained formula supplies an analytic reference for the Smolin HS-measure figure and the nearest-state input to the witness displayed immediately following the conjecture (lines 689–699).

## Gap

The bounded literature check recorded in #20844 attributes the following readings to the orchestrator:

- The arXiv abstract page lists only v1; the DOI resolves to the Phys. Rev. A article.
- OpenAlex work `W7213472887` reports zero citing works.
- A web search for the Hilbert–Schmidt distance of noisy Smolin states found no closed form or settlement.
- The repository search found no issue for the arXiv identifier and no Smolin-state module on `dev`.

`not-found-in-searched-scope`.

The issue distinguishes the known separability threshold and two-pair decomposition from the target: the exact distance formula with attainment. The v1 source retains the conjecture and describes numerical support at line 689. The bounded search does not establish worldwide novelty or priority.

## Route

Write $S=\sigma_x^{\otimes4}+\sigma_y^{\otimes4}+\sigma_z^{\otimes4}$ and $\rho_p=\mathcal N_p(\rho_S)=(I+pS)/16$.

1. **A fully separable boundary point.** For each $A\in\{\sigma_x,\sigma_y,\sigma_z\}$ put $P_{A,\pm}=(I\pm A)/2$. The average of the eight products $P_{A,s_1}\otimes P_{A,s_2}\otimes P_{A,s_3}\otimes P_{A,s_4}$ with $s_1s_2s_3s_4=1$ is $(I+A^{\otimes4})/16$. Averaging over the three axes gives $\rho_{1/3}$. For $0\le p\le1/3$, the identity $\rho_p=3p\rho_{1/3}+(1-3p)I/16$ gives full separability.
2. **A separating linear functional.** Pauli orthogonality gives $\operatorname{tr}S=0$, $\operatorname{tr}(S^2)=48$ and $\operatorname{Re}\operatorname{tr}(S\rho_p)=3p$. The three Hermitian involutions $B_j=\sigma_j^{\otimes3}$ anticommute in pairs. For a three-qubit density $b$, put $t_j=\operatorname{Re}\operatorname{tr}(B_jb)$, $T=\sum_jt_jB_j$ and $q=\sum_jt_j^2$. Then $T^2=qI$, $\operatorname{Re}\operatorname{tr}(Tb)=q$, and positivity gives $0\le\operatorname{tr}((T-I)^\dagger(T-I)b)=1-q$. The one-qubit Bloch bound and Cauchy–Schwarz yield $\operatorname{Re}\operatorname{tr}(S(a\otimes b))\le1$. Linearity extends this to every finite separable mixture for $\{1\}:\{2,3,4\}$.
3. **A sharp lower bound and an attaining state.** For $p>1/3$ and every such separable $\sigma$, $3p-1\le\operatorname{Re}\operatorname{tr}(S(\rho_p-\sigma))\le\sqrt{48}\,\|\rho_p-\sigma\|_{\mathrm{HS}}$. Since $\rho_p-\rho_{1/3}=(p-1/3)S/16$, its distance is exactly $(\sqrt3/4)(p-1/3)$. The lower bound is attained at $\rho_{1/3}$. At and below the threshold, $\rho_p$ itself attains zero.
4. **Refinement of partitions.** Grouping product factors gives $\mathrm{SEP}(1:2:3:4)\subseteq\mathrm{SEP}(1:2:34)\subseteq\mathrm{SEP}(1:234)$. The same fully separable candidate and the same lower bound give all three least-distance assertions.
5. **The two-pair partition.** With $\Pi_\mu$ the four Bell projectors, the reindexed Smolin matrix is $\frac14\sum_{\mu=0}^3\Pi_\mu\otimes\Pi_\mu$. The module verifies this identity through the Bell projectors' signed Pauli expansions. Mixing with $I/16$ preserves two-pair separability for $p\in[0,1]$, so $\rho_p$ attains distance zero.

## Falsifier

A mismatch of states, partitions, norms or attainment would prevent the formal statement from answering the source. The module fixes these explicitly:

- `Q` is $\mathrm{Fin}\,2\times(\mathrm{Fin}\,2\times(\mathrm{Fin}\,2\times\mathrm{Fin}\,2))$; `smolin` and `noisy` are exactly the matrices above, using the imported Pauli family `sigma`.
- `IsDensity` means positive semidefinite with trace one. Imported `IsSeparable`, with the factors determined by `Q`, means finite convex mixtures of products of a one-qubit and a three-qubit density matrix.
- `SepOneOneTwo` and `SepFull` are real convex hulls of products of density matrices on the displayed blocks. `SepTwoTwo` reindexes both matrix coordinates with the product-associating equivalence and applies bipartite `IsSeparable` to the two pairs.
- `hsDist X Y` is $\sqrt{\operatorname{Re}\operatorname{tr}((X-Y)^\dagger(X-Y))}$, without an extra factor or a square. `f` is zero for $p\le1/3$ and $(\sqrt3/4)(p-1/3)$ otherwise.
- `claim` restricts $p$ to $[0,1]$. Each `IsLeast` asserts membership in the set of actual distances and a lower bound for every member. It therefore includes an attaining separable matrix, rather than merely a bound on an infimum. No `sInf`, `sSup` or `iInf` is used to encode these minima.

The source's product-pure-state convention and the local density factors used here agree by finite spectral decomposition of each local factor; this identification is an argument, not an additional assertion of `result`. The two-pair zero-distance case is separate from the conjectured positive branch.

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance.lean` (536 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance.lean.json`, statement `sha256:d006579912e2b58bfe8faf68830526b72a23d7654ab3ab0fb6b884e6da808726`.

Declaration statements:

- `result`: `sha256:29ebd21b7384cfed23de12a50746a266c0a506b293973301f5d9149b752bade7`;
- `claim`: `sha256:80e5b1b8afd6422fde3925bb4239fa31013dabfd347b5b79db531bc33b64a1ab`.

## Triage

Tier 1: a numerically supported conjecture of a 2026 paper, preregistered in issue #20844 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every real $p\in[0,1]$, the sets of Hilbert–Schmidt distances from `noisy p` to matrices satisfying `IsSeparable`, membership in `SepOneOneTwo`, and membership in `SepFull` each have least element $f(p)$; the corresponding distance set for `SepTwoTwo` has least element zero. Each least element is attained. These are the four representative partitions defined above. The type of `result` does not specify which matrix attains a minimum or assert uniqueness.

**Auxiliary steps proved inside the module** (on the proof path of `result`, not conclusions of it): $\operatorname{tr}S=0$, $\operatorname{tr}(S^2)=48$, the eight-term parity-mixture identity for each of the three axes, and the four-term Bell-product identity.

**Hand computation from the definitions, not formalized:** for $p\ge1/3$, $\|\rho_p-\rho_{1/3}\|_{\mathrm{HS}}^2=\frac{48}{256}(p-\tfrac13)^2=\frac3{16}(p-\tfrac13)^2$. At $p=1/2,2/3,5/6,1$ this is $1/192,1/48,3/64,1/12$, and for $W=(I-S)/\sqrt{48}$, $\operatorname{tr}(W\rho_p)=(1-3p)/\sqrt{48}$.

**Argued, not formalized**.

- *Decisive mechanism and sharpness.* The fully separable point $\sigma_\star=\rho_{1/3}$ lies on the supporting hyperplane $\operatorname{Re}\operatorname{tr}(S\sigma)=1$ of the singleton-versus-three separable set. The displacement $\rho_p-\sigma_\star$ is a nonnegative multiple of its normal $S$ for $p\ge1/3$. Thus both the supporting-functional bound and Hilbert–Schmidt Cauchy–Schwarz are saturated. Every set $K$ with $\mathrm{SEP}(1:2:3:4)\subseteq K\subseteq\mathrm{SEP}(1:234)$ has the same attained distance on $[0,1]$: its candidate belongs to the smaller set, while every competitor obeys the larger set's lower bound. Convexity of $K$ is not needed for this argument.
- *Uniqueness of the candidate.* For $p>1/3$, put $t=p-1/3$ and let $\sigma\in\mathrm{SEP}(1:234)$. Expansion of the squared norm gives $\|\rho_p-\sigma\|_{\mathrm{HS}}^2=f(p)^2+\|\sigma_\star-\sigma\|_{\mathrm{HS}}^2+\frac{t}{8}(1-\operatorname{Re}\operatorname{tr}(S\sigma))$. The last two terms are nonnegative, so equality at the minimum forces $\sigma=\sigma_\star$. For $p\le1/3$, zero distance forces $\sigma=\rho_p$. For the two-pair set, the same zero-norm argument makes $\rho_p$ the unique minimizer throughout $[0,1]$. These are ordinary matrix arguments; uniqueness is not a clause of `result`.
- *Local-factor convention.* A local density matrix has a finite spectral decomposition $a=\sum_i\lambda_i|u_i\rangle\langle u_i|$ with nonnegative coefficients summing to one and unit eigenvectors. Expanding the tensor products of such decompositions replaces every product of mixed local densities by a finite convex mixture of products of pure local densities: the new weights are products of the local weights and still sum to one. Conversely, each pure local density is a density matrix. Thus the source's convention and the module's convention specify the same sets.
- *Relabelled partitions.* A permutation of the four qubits is implemented by a unitary permutation matrix. It fixes each $\sigma_j^{\otimes4}$ and $I$, preserves the HS norm by cyclicity of trace, and sends finite product decompositions bijectively to the corresponding relabelled decompositions. Transporting candidates and competitors therefore gives the same formulas for every relabelling of the four representatives. This transport is not stated by `result`.
- *Effect on the source's witness construction.* The witness at lines 691–693 uses $\sigma_\star-\rho_S=-S/24$, $\operatorname{tr}(\sigma_\star S)=1$ and $\|\sigma_\star-\rho_S\|_{\mathrm{HS}}=\sqrt{48}/24$, so it simplifies to $W=(I-S)/\sqrt{48}$. It has nonnegative expectation on each of the three separable sets, zero expectation at $\sigma_\star$, and expectation $-f(p)$ on $\rho_p$ for $p>1/3$. Its trace-free part has HS norm one. For fixed $p>1/3$ and any Hermitian $U$ with trace-free norm at most one, a gap $g$ satisfying $g\le\operatorname{tr}(U(\sigma-\rho_p))$ for every separable $\sigma$ obeys $g\le\operatorname{tr}(U(\sigma_\star-\rho_p))\le\|\sigma_\star-\rho_p\|_{\mathrm{HS}}=f(p)$ by Cauchy–Schwarz and the zero trace of $\sigma_\star-\rho_p$. Thus $W$ attains the maximal gap $g=f(p)$. The exact distance and candidate supply the Smolin instance's closest-state justification and an exact reference curve for the source's figure. The source's phrase “across any partition” (line 689) must exclude two-pair separability: $\rho_p$ is already separable there, and $W$ has negative expectation on the separable state $\rho_S$. The source's general witness theorems have separate proofs (lines 101–112 and 359–420); this module does not formalize those general results or certify DREAM's global convergence.
- *Neighbouring question, open here.* For noise that changes the three Pauli-correlation coefficients unequally, the displacement need not remain parallel to $S$. A nearest-state formula in that setting is not supplied by this settlement; no general answer is asserted.

## ASSUMED-UNVERIFIED

The literature check is bounded to the readings and search scope reported by the orchestrator in #20844. The OpenAlex count, search-engine results, repository-wide novelty search, arXiv version listing and DOI-resolution reading were not independently reproduced here. Neither those readings nor the source's numerical support establish exhaustive worldwide novelty or priority. The source TeX and its conjecture were directly checked; the earlier Smolin and separability-threshold papers cited by it were not independently read.

The hand computation and all arguments under “Argued, not formalized” are not additional Lean conclusions. In particular, `result` does not assert the named closest-state formula, uniqueness, arbitrary intermediate sets, permutation transport, equivalence of pure and mixed local-factor conventions, or witness optimality. Their matrix arguments are given above or in the Route and Falsifier sections. The numerical data underlying the source's Smolin figure and its DREAM runs were not reproduced. The anisotropic-noise question remains open here. The mathematical scope is four qubits, the four specified separability sets, white noise and $p\in[0,1]$.
