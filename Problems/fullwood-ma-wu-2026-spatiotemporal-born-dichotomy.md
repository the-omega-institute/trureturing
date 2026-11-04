---
slug: fullwood-ma-wu-2026-spatiotemporal-born-dichotomy
bibkey: fullwoodmawu2026spatiotemporalborn
doi: 10.1103/cw25-pqx1
url: https://arxiv.org/abs/2507.16919v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurements/SpatiotemporalBornRuleDichotomy.result
---

# The spatiotemporal Born rule for the LvN distribution has exactly two cases

## Problem

J. Fullwood, Z. Ma and Z. Wu, *The spatiotemporal Born rule is quasiprobabilistic*, arXiv:2507.16919v2; published as *Quasiprobabilistic nature of the spatiotemporal Born rule*, Phys. Rev. A 113, 032204 (2026). Section VI, final paragraph (`PRA_rev.tex`, line 577), asks the following. The source macro `\E` denotes $\mathcal E$.

> It is then natural to ask whether $\rho$ being maximally mixed or $\E$ being a discard-and-prepare channel is also a necessary condition for the existence of the spatiotemporal Born rule for the LvN distribution. While it is straightforward to show that this is indeed the case when $A$ consists of a single qubit, for systems of arbitrary dimension we leave it as an open question.

Issue [#21996](https://github.com/the-omega-institute/trureturing/issues/21996) fixes the statement for all positive finite input and output dimensions. For every $d,e\ge1$, every density matrix $\rho\in M_d(\mathbb C)$ and every CPTP complex linear map $\mathcal E:M_d(\mathbb C)\to M_e(\mathbb C)$,

$$
\begin{aligned}
&\exists W\in M_{de}(\mathbb C)\;\forall P,Q\text{ orthogonal projections},\quad
\operatorname{tr}[W(P\otimes Q)]
 =\operatorname{tr}[\mathcal E(P\rho P)Q] \\
&\qquad\Longleftrightarrow\quad
\rho=I_d/d\quad\text{or}\quad
\exists\sigma\in M_e(\mathbb C),\quad
\sigma\succeq0,\quad\operatorname{tr}\sigma=1,\quad
\forall X\in M_d(\mathbb C),\quad\mathcal E(X)=\operatorname{tr}(X)\sigma.
\end{aligned}
$$

Here $P$ acts on the input and $Q$ on the output; an orthogonal projection is a self-adjoint idempotent. A density matrix is positive semidefinite with trace one. Complete positivity means positivity of every finite amplification, and trace preservation is required on every matrix. The same $W$ must work for all projections, without a positivity, Hermiticity or normalization assumption on $W$. This equivalence is proved.

The source defines the LvN distribution by $\mathbf P(i,j)=\operatorname{tr}[\mathcal E(P_i\rho P_i)Q_j]$ in Section II (`PRA_rev.tex`, lines 247–250), and its universal Born representation in Section VI, lines 534–537. The [literature note](../Library/Observer/fullwoodmawu2026spatiotemporalborn.md) supplies the corresponding source locators.

## Motivation

A fixed bipartite operator gives a trace pairing additive in each measurement argument. The LvN distribution includes disturbance from the initial projection and need not have that additivity. The question asks exactly which state–channel pairs remove this obstruction for every projective measurement, rather than for selected compatible measurements. The answer classifies the exceptional cases in which the sequential probabilities themselves admit the representation.

## Gap

The v2 source retains the question at line 577. The bounded literature check recorded in #21996 reports:

- The orchestrator's web search compared the question with related work including arXiv:2603.21793 and arXiv:2609.24680, without finding this characterization.
- The search contributor reported inspecting six citing works without finding a settlement, and reported that Fullwood–Yang, arXiv:2512.08068v1, Example 4.2, describes the related necessity as still open. MathDB requests were blocked.
- The orchestrator's repository search found no earlier issue, module, Library note or dossier mentioning arXiv:2507.16919.

`not-found-in-searched-scope`. These literature-search readings are attributed reports from #21996, not an exhaustive novelty claim.

## Route

All matrices and maps below are over $\mathbb C$, with finite dimensions $d,e\in\mathbb N$ and $\mathcal E:M_d(\mathbb C)\to M_e(\mathbb C)$ complex linear. Write $F_{uv}=uv^*$ and denote by (B) the identity

$$
\mathcal E(P\rho+\rho P)=2\mathcal E(P\rho P)
\qquad\text{for every self-adjoint projection }P.
$$

1. **Additivity gives (B).** `projections_span` states that self-adjoint projections span $M_n(\mathbb C)$ over $\mathbb C$ for every natural $n$. `trace_separates` applies to any $X\in M_e(\mathbb C)$ whose pairing $\operatorname{tr}(XQ)$ vanishes for every self-adjoint projection $Q$, and concludes $X=0$. For arbitrary $\rho$ and $\mathcal E$ as above, `born_identity` assumes `BornRuleExists ρ ε` and concludes (B): substitute the representation for $I$, $P$ and $I-P$, use $I=P+(I-P)$, and separate by all output projections.

2. **Distinct eigenvalues force equal diagonal images and zero cross images.** `two_eigenvector` assumes $\rho$ is Hermitian, (B), real numbers $r\ne s$, and vectors $u,v$ satisfying $\rho u=ru$, $\rho v=sv$, $u^*u=v^*v=1$ and $u^*v=v^*u=0$. It concludes
   $\mathcal E(F_{uu})=\mathcal E(F_{vv})$ and $\mathcal E(F_{uv})=\mathcal E(F_{vu})=0$.
   Under precisely these hypotheses the proof uses the normalized ray projectors of $u+v$, $3u+4v$ and $3u+4iv$, whose squared norms are $2$, $25$ and $25$. Its expansion lemma `two_ray_equation` has the same Hermiticity, (B), eigenvector and orthonormality hypotheses, with real $r,s,a,b$, $a^2+b^2\ne0$ and a complex phase $z$ satisfying $\overline z z=1$; it does not require $r\ne s$. The three choices $(a,b,z)=(1,1,1),(3,4,1),(3,4,i)$ supply the equations used by `two_eigenvector`.

3. **Degenerate eigenspaces retain no cross images.** `degenerate_offdiag` assumes Hermitian $\rho$, (B), vectors $v_i$ indexed by $\mathrm{Fin}\,d$ with $v_i^*v_j=\delta_{ij}$, real $r_i$ with $\rho v_i=r_iv_i$, and one matrix $\sigma$ satisfying $\mathcal E(F_{v_i v_i})=\sigma$ for every $i$. For indices $i,j,k$ with $i\ne j$, $r_i=r_j$ and $r_i\ne r_k$, it concludes $\mathcal E(F_{v_i v_j})=0$. The proof compares $(v_i+zv_j)/\sqrt2$ with $v_k$ for $z=1,i$. The existence of such a $k$ is essential to this step.

4. **Assemble the eigenbasis.** `eigenbasis_assembly` assumes `IsDensity ρ`, `IsCPTP ε`, $1\le d$ and (B). If all eigenvalues coincide, trace one gives $\rho=I_d/d$. Otherwise two distinct eigenvalues provide a comparison vector for every eigenspace. Steps 2 and 3 give a common diagonal image $\sigma$ and zero off-diagonal images. Expansion in the orthonormal eigenbasis gives $\mathcal E(X)=\operatorname{tr}(X)\sigma$ for every matrix $X$. Complete positivity gives $\sigma\succeq0$ and trace preservation gives $\operatorname{tr}\sigma=1$. The lemma concludes $\rho=I_d/d$ or `DiscardPrepare ε`.

5. **Construct both representations.** For $d,e\ge1$, `born_of_scalar` applies to every complex linear $\mathcal E$ and represents $\rho=(1/(d:\mathbb C))I_d$ by
   $W=(1/(d:\mathbb C))\sum_{i,j}E_{ij}\otimes\mathcal E(E_{ji})$, where $E_{ij}$ are coordinate matrix units. `born_of_discard` applies to every $\rho\in M_d(\mathbb C)$ and every complex linear $\mathcal E$ satisfying `DiscardPrepare ε`, namely a fixed density matrix $\sigma$ with $\mathcal E(X)=\operatorname{tr}(X)\sigma$ for all $X$; it uses $W=\rho\otimes\sigma$. In both constructions the input projection satisfies $P^2=P$; cyclicity of trace gives $\operatorname{tr}(P\rho P)=\operatorname{tr}(\rho P)$ in the second. `result` combines these lemmas under the density, CPTP and positive-dimension hypotheses of `claim`.

## Falsifier

A mismatch would arise if the representing operator could depend on the measurements, if only rank-one or one fixed measurement were tested, or if positivity of $W$ were imposed. `BornRuleExists` instead quantifies over one complex matrix $W$ and all pairs of self-adjoint projections. Every projection $P$ belongs to the projective measurement $\{P,I-P\}$, and each outcome of a projective measurement is a projection; this matches the source's universal measurement condition.

`DiscardPrepare` specifies the map on all complex matrices, not merely on a selected input state. The dimensions $d$ and $e$ are independent and positive in `claim`; zero-dimensional inputs are outside its assertion. The two alternatives are inclusive. For $d=1$ the maximally mixed alternative already covers the unique density matrix, so the argument does not require two distinct eigenvalues in that case.

## Evidence

The canonical source is `D5/S3/Quantum/Measurements/SpatiotemporalBornRuleDichotomy.lean` (457 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurements/SpatiotemporalBornRuleDichotomy.lean.json`, statement `sha256:be13a90e55fe27b5cec3bd6ec48fa00ab77bc058df40f15dd652fb07eb82a39e`.

Declaration statements:

- `result`: `sha256:3a68b3a67c20a3ee1297a57ee8782c52e8751c2fb0c8f45b1662510841d1c48f`;
- `claim`: `sha256:a0b357db442f1b375e854348d512e5ee2b30093cd8774f3eee1ebe3f68bf1645`.

## Triage

Tier 1 question of Fullwood, Ma and Wu (arXiv:2507.16919v2; journal publication 2026), preregistered in issue #21996 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for all natural $d,e\ge1$, every positive-semidefinite trace-one $\rho\in M_d(\mathbb C)$ and every CPTP complex linear map $\mathcal E:M_d(\mathbb C)\to M_e(\mathbb C)$, one complex matrix $W\in M_{de}(\mathbb C)$ represents $\operatorname{tr}[\mathcal E(P\rho P)Q]$ as $\operatorname{tr}[W(P\otimes Q)]$ for all self-adjoint projections $P,Q$ if and only if $\rho=I_d/d$ or there is a positive-semidefinite trace-one $\sigma\in M_e(\mathbb C)$ with $\mathcal E(X)=\operatorname{tr}(X)\sigma$ for every $X\in M_d(\mathbb C)$.

**Computed, not formalized.** Exact rational matrix arithmetic gives two $d=e=2$ examples:

- For $\rho=\operatorname{diag}(3/4,1/4)$ and the identity channel, take $P=\tfrac12\begin{pmatrix}1&1\\1&1\end{pmatrix}$ and $Q=\operatorname{diag}(1,0)$. The LvN values for input projections $P$, $I-P$ and $I$ are respectively $1/4$, $1/4$ and $3/4$, giving a coarse-graining defect $1/4$. For the same state and channel, the fixed computational-basis measurements at both times are represented by $W=\tfrac34|00\rangle\langle00|+\tfrac14|11\rangle\langle11|$, with joint values $(3/4,0,0,1/4)$. These calculations concern only the specified measurements and matrices.
- For $\rho=I_2/2$ and the identity channel, the scalar construction gives $W=S/2$, where $S$ swaps the two factors. Its trace is $1$ and $W(0,1,-1,0)^{\mathsf T}=-\tfrac12(0,1,-1,0)^{\mathsf T}$. This representing operator is not positive semidefinite.

**Argued, not formalized.**

- *Decisive mechanism and extent.* For arbitrary natural $d,e$, arbitrary complex $\rho$, and complex linear $\mathcal E$ with `BornRuleExists ρ ε`, `born_identity` gives (B) without density or CPTP assumptions. For Hermitian $\rho$, complex linear $\mathcal E$ satisfying (B), distinct real $r,s$, and $u,v$ with $\rho u=ru$, $\rho v=sv$, $u^*u=v^*v=1$ and $u^*v=v^*u=0$, `two_eigenvector` forces equal diagonal images and zero cross images. For Hermitian $\rho$, complex linear $\mathcal E$ satisfying (B), an indexed orthonormal family $v_i$ with real eigenvalues $r_i$ and $\rho v_i=r_iv_i$, a common image $\mathcal E(F_{v_i v_i})=\sigma$ for every $i$, and indices $i\ne j$ with $r_i=r_j\ne r_k$, `degenerate_offdiag` also kills the equal-eigenvalue cross image. The third eigenvector is what closes the degeneracy gap. Stability under approximate Born representations and extensions to infinite dimensions remain open here.
- *Both branches are needed.* At $d=e=2$, $\rho=I_2/2$ and the identity channel satisfy the first alternative; the channel is not discard-and-prepare, because it fixes the nonzero traceless matrix $\operatorname{diag}(1,-1)$, whereas a discard-and-prepare map annihilates it. Conversely, a pure input state and the channel $X\mapsto\operatorname{tr}(X)|0\rangle\langle0|$ satisfy the second alternative with a nonmaximally mixed input. This channel is CPTP: the Kraus matrices $|0\rangle\langle0|$ and $|0\rangle\langle1|$ sum to that map and their adjoint products sum to $I_2$. Thus neither alternative alone characterizes existence.
- *Measurement scope is necessary.* For any fixed projective measurement $\{P_i\}$, any density matrix $\rho$, and any CPTP $\mathcal E$, set $A_i=\mathcal E(P_i\rho P_i)$ and $W=\sum_{i:P_i\ne0}(P_i/\operatorname{tr}P_i)\otimes A_i$. Nonzero projections have positive trace, and $\operatorname{tr}(P_iP_j)=\delta_{ij}\operatorname{tr}P_i$, so $\operatorname{tr}[W(P_j\otimes Q)]=\operatorname{tr}(A_jQ)$ for every output projection $Q$. A zero $P_j$ contributes zero on both sides. Thus fixing the initial measurement admits a representation for arbitrary state–channel pairs and cannot give the universal dichotomy.
- *Effect on the source's equivalence theorem.* Section VI (`PRA_rev.tex`, lines 539–556) states that existence of the LvN representation, equality of LvN and TMH for every TPSM scenario, vanishing of the modification term for every scenario, annihilation of every binary-measurement disturbance, and coarse-graining additivity are equivalent. Combining those source equivalences with `result` classifies each condition by the same two alternatives. For the disturbance formulation the bridge is explicit: $\rho-P\rho P-(I-P)\rho(I-P)=P\rho+\rho P-2P\rho P$, so its image vanishes exactly when (B) holds. This combination with the source theorem is not a separate Lean conclusion of `result`.
- *Other source statements.* The question follows the Section VI equivalence theorem; that theorem and the Section III universal representation of TMH quasiprobabilities are stated and proved without assuming an affirmative answer. Their proofs therefore require no replacement. Proposition 1's sufficient conditions for an individual disturbance term to vanish retain their individual-measurement scope. The settlement supplies the missing necessity only for the universal condition. It does not promote the source's discussion of multi-time scenarios (`PRA_rev.tex`, line 587) to a multi-time dichotomy; that extension remains open here.

## ASSUMED-UNVERIFIED

The bounded literature check in #21996 does not establish exhaustive worldwide novelty or priority. The web-search results, the six citing-work readings, the Fullwood–Yang reading, the related-paper comparisons and the reported MathDB blockage were not independently reproduced. The preregistration's negative repository-search reading was not rerun as a novelty audit. The source checked directly is arXiv:2507.16919v2, `PRA_rev.tex` (MD5 `ccc824023e2958b612ebb8c2be819e2f`); the publisher's article text was not read, so identity of its wording with v2 is unverified.

The rational matrix calculations and the arguments in the corresponding labelled groups are not formalized. `result` states the existence dichotomy, not uniqueness or positivity of $W$, a quantitative approximation theorem, an infinite-dimensional extension or a multi-time extension. No such additional formal conclusion is claimed.
