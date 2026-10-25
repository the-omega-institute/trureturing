---
slug: zhang-nechita-2022-projective-test-channel-compatibility-refutation
bibkey: zhangnechita2022fisherchannelincompatibility
doi: 10.3390/e24060805
url: https://arxiv.org/abs/2204.09963v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/ProjectiveTestChannelCompatibilityRefutation.result
---

# Compatible projective tests do not imply compatible quantum channels

## Problem

Qing-Hua Zhang and Ion Nechita, *A Fisher information-based incompatibility criterion for quantum channels*, Entropy 24(6), 805 (2022), DOI 10.3390/e24060805, arXiv:2204.09963v1, Section 4, conjecture immediately following Lemma `lem:channel-POVM-compatible` (`article.tex`, lines 263–265):

> Consider two quantum channels $\Phi, \Psi: \mathcal L(H_d) \to \mathcal L(H_d)$ such that, for all orthonormal bases $\mathbf e = (e_1, \ldots, e_d)$, $\mathbf f = (f_1, \ldots, f_d)$ of $\mathbb C^d$, the POVMs
>
> $\Big[ \Phi^*(|e_i\rangle\langle e_i|) \Big]_{i=1}^d \quad \text{ and } \quad \Big[ \Psi^*(|f_j\rangle\langle f_j|) \Big]_{j=1}^d$
>
> are compatible. Then, $\Phi$ and $\Psi$ are compatible channels.

The source's `\ketbra` macro is expanded in the displayed quotation. The source archive member `article.tex` has MD5 `614f0961ea15b65fb0b83ac83bd3fffb`.

Here channels are completely positive, trace-preserving complex linear maps. Two POVMs are compatible when a positive normalized family indexed by both outcome sets has them as its marginals. Two channels are compatible when a single channel to the tensor product of their outputs has them as its partial-trace marginals on every input matrix. These definitions are in the source at lines 124–146 and 179–199 and in [the literature note](../Library/QuantumContext/zhangnechita2022fisherchannelincompatibility.md).

Issue [#21608](https://github.com/the-omega-institute/trureturing/issues/21608) fixes the reading: for every positive dimension and every pair of channels on that space, compatibility of the two induced POVMs for every pair of orthonormal bases implies channel compatibility. This is refuted by two copies of the qubit depolarizing channel $\Phi_{7/10}$.

## Motivation

A basis measurement is a classical test of a channel's output. The conjecture asks whether passing every pair of such tests suffices for a joint quantum output. The source's Fisher information criterion uses incompatible induced measurements to witness incompatible channels. The converse would make projective tests a complete characterization of channel compatibility.

## Gap

The bounded literature check recorded in #21608 reports:

- The orchestrator found only arXiv v1; its TeX retains the conjecture. The published version retains it as Conjecture 1 according to the search report cited in the issue (PMC9222584).
- Crossref reported three citing works and Semantic Scholar listed four: arXiv:2606.23647, arXiv:2410.20117, arXiv:2303.02662, and Fei–Li–Luo, Entropy 25, 463 (2023). In their TeX sources, arXiv:2303.02662 cites the paper among existing channel-compatibility criteria (`compatible-unitarity-pairs.tex`, l. 173), arXiv:2606.23647 in its introduction's list of works on channel incompatibility (`main_updated.tex`, l. 170), and arXiv:2410.20117 when introducing Schur channels (`Fidelity_preservation_for_mixed_unitary_quantum_channels.tex`, l. 335); none addresses the conjecture. The search report describes Fei–Li–Luo as summarizing the criterion without settling the conjecture.
- The issue records no prior repository issue, module, Library note or dossier on this conjecture. It identifies the qubit joint-measurability and cloning bounds as classical ingredients, while a statement connecting them to a refutation was `not-found-in-searched-scope`.

These are bounded search reports, not an exhaustive novelty claim.

## Route

All helper names below refer to the canonical module; they are private except for `result` and the definitions `basisPOVM`, `ChannelCompatible` and `claim`.

1. **The channel.** `depol` is `depolarized LinearMap.id (3 / 10)` on $M_2(\mathbb C)$, hence
   $\Phi(X)=\frac7{10}X+\frac3{20}\operatorname{Tr}(X)I_2$.
   With no additional hypotheses, the frozen `dep_cptp` of `D5/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity.lean`, applied at $\eta=7/10$, proves this fixed map is CPTP; its Pauli probabilities are $(31/40,3/40,3/40,3/40)$; `depol_dual` proves its trace dual equals itself.
2. **Every pair of bases has a parent.** For arbitrary $U,V\in\operatorname{U}(2)$ and $a,b\in\{0,1\}$, put $E_a=|U_a\rangle\langle U_a|$, $F_b=|V_b\rangle\langle V_b|$, $A_a=2E_a-I_2$ and $B_b=2F_b-I_2$. For every such unitary and outcome, `effect_facts` proves the projector is Hermitian, has trace one, is idempotent, and the two projectors sum to $I_2$; `centered_facts` proves the centered matrices are Hermitian, traceless, square to $I_2$, and sum to zero within each basis. For any complex $2\times2$ matrices $A,B$ with $\operatorname{Tr}A=\operatorname{Tr}B=0$, `traceless_anticommutator` gives $AB+BA=\operatorname{Tr}(AB)I_2$.

   `parent_positive`, for every $U,V\in\operatorname{U}(2)$ and $a,b\in\{0,1\}$, proves positivity of
   $G_{ab}=\frac14[(1+\frac{49}{200}\operatorname{Tr}(A_aB_b))I_2+\frac7{10}(A_a+B_b)]$.
   In its proof, $K=A_a+B_b$ satisfies $K^2=(2+\operatorname{Tr}(A_aB_b))I_2$. Thus $\tau=\operatorname{Tr}(A_aB_b)$ is real and $\tau\ge-2$. Put $\alpha=1+49\tau/200>0$, $c=1/50+2401\tau^2/40000>0$ and $H=\alpha I_2+7K/10$. The identity $H^*H+cI_2=2\alpha H$ expresses $H$ as a positive multiple of a positive semidefinite matrix.

   `parent_marginals`, for every $U,V\in\operatorname{U}(2)$, proves $\sum_{a,b}G_{ab}=I_2$, $\sum_bG_{ab}=\Phi^*(E_a)$ for every $a$, and $\sum_aG_{ab}=\Phi^*(F_b)$ for every $b$. `all_projective_tests`, with exactly these arbitrary unitary-basis parameters, concludes compatibility of the two POVMs.
3. **A joint channel would violate a positive witness.** For any complex linear map $J:M_2(\mathbb C)\to M_2(\mathbb C)\otimes M_2(\mathbb C)$ satisfying `IsCPTP J`, `jointChoi_positive` and `jointChoi_trace` prove that $R=\frac12\operatorname{Choi}(J)$ is positive semidefinite and has trace one. Indices are ordered as $((a,b),r)$, with outputs $a,b$ and reference $r$.

   Let $P$ be the Bell projection on the first output and reference, tensored with the identity on the other output, and $Q$ the corresponding second-output projection. For any such linear map $J$ satisfying both marginal identities $\operatorname{Tr}_2J(X)=\Phi(X)$ and $\operatorname{Tr}_1J(X)=\Phi(X)$ for every complex input matrix $X$, `jointChoi_overlaps` proves $\operatorname{Tr}(RP)=\operatorname{Tr}(RQ)=31/40$; this lemma does not assume CPTP.

   `witness_positive`, with no hypotheses, proves $W=\frac32I_8-P-Q\succeq0$ by an explicit Gram decomposition. Combining the CPTP and both marginal hypotheses, `no_joint_channel` obtains
   $0\le\operatorname{Tr}(RW)=\frac32-\frac{31}{40}-\frac{31}{40}=-\frac1{20}$,
   a contradiction. `result` applies the proposed universal implication at $d=2$ to this fixed map twice.

## Falsifier

The settlement would miss the source conjecture if either compatibility predicate or the channel convention differed materially from the source. The module uses:

- `basisPOVM φ U i = φ.dual (measurementProjector U i)`, with the columns of $U$ parameterizing all ordered orthonormal bases. The trace dual obeys $\operatorname{Tr}(\phi(X)A)=\operatorname{Tr}(X\phi^{\mathrm{dual}}(A))$. For CPTP maps a Kraus representation gives both this trace dual and the source's Hilbert–Schmidt adjoint as $A\mapsto\sum_k K_k^*AK_k$. In particular, `depol_dual` identifies the counterexample's dual exactly.
- `IsCPTP`: positivity at every finite amplification and trace preservation on every complex matrix. `Compatible` requires positive normalized POVMs and a positive normalized joint POVM with both prescribed marginals. `ChannelCompatible` requires a CPTP joint map with both partial-trace identities for every input matrix.
- The source's $\Phi_t=t\,\mathrm{id}+(1-t)\Delta$, with $\Delta(X)=\operatorname{Tr}(X)I_2/2$, at $t=7/10$. The module's `depolarized` argument $3/10$ is the noise fraction $1-t$.

`claim` quantifies over every natural dimension, including zero. The counterexample uses dimension two, so it also refutes the preregistered positive-dimensional reading. The antecedent is proved for all unitary bases, rather than for a finite sample. The conclusion excludes every CPTP joint map, including nonsymmetric ones.

## Evidence

The canonical source is `D5/S3/Quantum/QuantumChannels/ProjectiveTestChannelCompatibilityRefutation.lean` (373 lines).

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/QuantumChannels/ProjectiveTestChannelCompatibilityRefutation.lean.json`, statement `sha256:4fea9a0e2b483bf2e1689a863b47555a458a544b392f28cac4854c49b2c586d6`.

Declaration statements:

- `result`: `sha256:a5baf7c92bba00302635ab2d34d9d4d23e0c8d9a72f2747637490e1e5850d64d`;
- `claim`: `sha256:08a34ce2e54e86c3b2e12bfd72ebd79431ef39bb340fd18b45d6e2a08c2f0064`.

## Triage

Tier 1 conjecture of a 2022 journal paper, preregistered in issue #21608 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the universal implication `claim` is false: it is not the case that, for every natural dimension and every pair of CPTP maps on that matrix algebra, compatibility of their induced POVMs for every pair of unitary bases implies the existence of a CPTP joint map with the two prescribed marginals.

**Computed, not formalized.** Exact SymPy calculations give:

- At $t=7/10$, the normalized channel Choi matrix has eigenvalues $31/40$ once and $3/40$ three times, and Bell overlap $31/40$.
- $P+Q$ has eigenvalues $0,1/2,3/2$ with multiplicities $4,2,2$; $W$ has eigenvalues $0,1,3/2$ with multiplicities $2,2,4$. An entrywise calculation verifies the Gram decomposition used by `witness_positive`.
- The witness gap is $-1/20$. The scalar parent-positivity polynomial, with $u=\operatorname{Tr}(AB)/2$, is $1/50+2401u^2/10000$.
- With a symbolic parameter $t$, the parent-positivity polynomial is $1-2t^2+t^4u^2$, the Bell overlap is $(1+3t)/4$, and the witness gap is $1-3t/2$. At $t=7/10$, $2t^2=49/50$.

These computations corroborate the certificates and provide symbolic expressions for the following argument; the module does not state a theorem about a variable $t$.

**Argued, not formalized.**

- *Mechanism and missing structure.* The hypothesis permits a different parent POVM for each pair of bases. A joint quantum channel requires one completely positive map accommodating all output observables. Positivity and normalization of the separately constructed parents do not supply that common map. In this counterexample the two required Bell overlaps would sum to $31/20$, beyond the witness bound $3/2$ for a positive trace-one joint Choi matrix.
- *A sufficient additional structure.* For channels on $M_d(\mathbb C)$ with $d\ge1$, suppose the test effects come from a single unital completely positive map $T:M_d(\mathbb C)\otimes M_d(\mathbb C)\to M_d(\mathbb C)$ satisfying $T(A\otimes I)=\Phi^*(A)$ and $T(I\otimes B)=\Psi^*(B)$ for every $A,B$. Write a Kraus representation $T(Z)=\sum_k L_k ZL_k^*$. Unitality says $\sum_kL_kL_k^*=I_d$, so the adjoint $T^*(X)=\sum_kL_k^*XL_k$ is completely positive and trace preserving. The same pairing gives the two partial-trace identities, so this stronger condition supplies a joint channel. Mere existence of the parents in the conjecture does not supply this structure.
- *A parameter interval, by a separate argument.* Let $0\le t\le1/\sqrt2$ and take arbitrary qubit basis projectors $E_a,F_b$. Set $A=2E_a-I_2$, $B=2F_b-I_2$, $K=A+B$ and $u=\operatorname{Tr}(AB)/2$. These matrices are Hermitian and traceless with $A^2=B^2=I_2$; entrywise expansion gives $AB+BA=2uI_2$, so $K^2=2(1+u)I_2$. Positivity of $K^2$ makes $u$ real and $u\ge-1$. Put $\alpha=1+t^2u\ge1-t^2\ge1/2$, $c=1-2t^2+t^4u^2\ge0$ and $H=\alpha I_2+tK$. Then $H^*H+cI_2=2\alpha H$, so $H/4\succeq0$, including when $c=0$. The four effects $G^{(t)}_{ab}=H/4$ sum to $I_2$, and summing either outcome cancels the centered terms from the other basis, giving $\Phi_t(E_a)$ and $\Phi_t(F_b)$. The map $\Phi_t$ is CPTP with Pauli probabilities $((1+3t)/4,(1-t)/4,(1-t)/4,(1-t)/4)$ and is its own adjoint. Thus every pair of these tests has a parent throughout this interval. A hypothetical joint channel has a positive trace-one normalized Choi matrix with each Bell overlap equal to $\frac14\sum_{i,j=0}^1\Phi_t(|i\rangle\langle j|)_{ij}=(1+3t)/4$ by the marginal identities; the same fixed positive witness yields $0\le1-3t/2$, excluding $t>2/3$. Consequently this argument gives counterexamples for $2/3<t\le1/\sqrt2$. Only the fixed value $7/10$ is settled by the module's `result`.
- *Nearby statements and the source's dependencies.* The forward implication of Lemma `lem:channel-POVM-compatible` survives: for compatible channels with a CPTP joint map $\Lambda$, applying its unital positive adjoint to the tensor products of basis projectors gives a positive normalized parent, and summing the other outcomes gives the required marginals. The source's main theorem `thm:incompatibility-criterion` explicitly derives its sufficient incompatibility criterion from this lemma and Proposition `prop:criterion-POVM-incompatible`, not from the conjecture (`article.tex`, lines 275–287). The Schur-channel and depolarizing-channel applications use that sufficient theorem; their dependence on it is not invalidated by refuting the converse. No theorem in the inspected source invokes the conjecture as a premise. In particular, Proposition `prop:depolarizing-compatible` assumes $N\le D_d$, $t_i\in[0,1]$ and $\sum_i t_i^2>1$; for two identical qubit channels the sufficient condition is $2t^2>1$ (lines 497–514). The counterexample has $2t^2=49/50$, outside that condition. The last corollary states self-incompatibility for $t>1/\sqrt K$ under $K\le\min(N,D_d)$ (lines 535–538); it does not assert a converse. The refutation rules out completeness of all projective tests for channel compatibility and does not contradict these one-way criteria.

## ASSUMED-UNVERIFIED

The literature check is bounded by the sources and citation listings reported in #21608 and does not establish exhaustive worldwide novelty or priority. The published-version reading, citation counts, citing-paper readings and prior-repository search recorded there were not independently reproduced here; the arXiv v1 TeX and its conjecture were directly checked. The search report's identification of the published conjecture as Conjecture 1 remains attributed to that report.

The exact SymPy computations, the interpretation of the trace dual as the source's adjoint, the common-map sufficient condition, the variable-parameter interval argument and the analysis of the paper's dependencies are not additional compiled declarations of this module. The formal settlement is `result : ¬ claim`. The conjecture with projective tests replaced by arbitrary POVMs, or by tests allowing ancillary systems, is not settled here. Whether either modification suffices without an explicit common completely positive extension remains open in this dossier.
