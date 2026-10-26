---
slug: ballesteros-et-al-2025-qdicke-closest-product
bibkey: ballesterosetal2025qsymmetric
doi: 10.1088/1751-8121/ae05da
url: https://arxiv.org/abs/2503.23554v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation.result
---

# A closest product vector to a q-Dicke state need not be q-symmetric

## Problem

A. Ballesteros, I. Gutierrez-Sagredo, J. de Ramón and J. J. Relancio, *Deformations of the symmetric subspace of qubit chains*, J. Phys. A 58, 405301 (2025), arXiv:2503.23554v3, subsection “Entanglement of q-symmetric states”, TeX member `newsubmission__1_.tex`, l. 1258:

> Therefore, the closest separable state to a $q$-symmetric state for two qubits is also $q$-symmetric. If we conjecture that a similar relation holds for arbitrary $q$-Dicke states, it would mean that we can construct whole new families of states whose multipartite entanglement has an analytic expression.

The optimization in that subsection is the ordinary overlap modulus over product vectors with every local factor normalized (l. 1234–1243). Write $|0\rangle=|\downarrow\rangle$ and $|1\rangle=|\uparrow\rangle$. For $q>0$, the three-qubit vectors at l. 581–582 are

$|D^1_3\rangle_q=(\sqrt q\,|001\rangle+|010\rangle+q^{-1/2}|100\rangle)/\sqrt{q+1+q^{-1}}$,

$|D^2_3\rangle_q=(\sqrt q\,|011\rangle+|101\rangle+q^{-1/2}|110\rangle)/\sqrt{q+1+q^{-1}}$.

Here $[3]_q=q+1+q^{-1}$ follows from the source's q-number at l. 469, with its undeformed convention at $q=1$. The source identifies $\mathrm{Sym}_q\mathcal H$ with the complex span of $|000\rangle$, $|D^1_3\rangle_q$, $|D^2_3\rangle_q$ and $|111\rangle$ (l. 586). These definitions are recorded in [the literature note](../Library/LieTheory/ballesterosetal2025qsymmetric.md).

Issue [#21970](https://github.com/the-omega-institute/trureturing/issues/21970) fixes the reading: for every real $q>0$, there exist unit $a,b,c\in\mathbb C^2$ such that $a\otimes b\otimes c$ maximizes $|\langle D^1_3|_q(a\otimes b\otimes c)\rangle|$ over all unit local factors and belongs to $\mathrm{Sym}_q\mathcal H$. This three-qubit, one-excitation instance of the conjecture is refuted.

## Motivation

The paper proposes transferring the simplification of geometric entanglement optimization for ordinary symmetric states to q-Dicke states. A q-symmetric closest product would justify restricting the search to that subspace and support the proposed analytic families. The question tests whether the paper's deformed symmetry controls optimization with the ordinary Hilbert-space norm.

## Gap

Issue #21970 records the bounded literature check before any Lean:

- the v3 TeX contains the conjecture in the applications subsection, whose introductory paragraph explicitly limits the rigor of the applications discussion (l. 1226);
- the orchestrator's web search for q-Dicke geometric measure, closest product states and q-symmetric subspaces found the source and older entanglement-entropy work, without a settlement;
- the preregistration reports no existing repository issue, module, literature note or dossier for arXiv:2503.23554;
- its reports that v1 and v2 omit the conjecture and that citing works contain no settlement were not independently reproduced here.

`not-found-in-searched-scope`.

## Route

All vectors and norms below are over the ordinary complex Euclidean spaces. The helper lemmas named here are private declarations of the module.

1. **The explicit overlap.** For arbitrary $a,b,c\in\mathbb C^2$, `overlap_four` expands the overlap at $q=4$, where $D=|D^1_3\rangle_4=(4|001\rangle+2|010\rangle+|100\rangle)/\sqrt{21}$:
   $\langle D,a\otimes b\otimes c\rangle=(4a_0b_0c_1+(2a_0b_1+a_1b_0)c_0)/\sqrt{21}$. For the same unrestricted $a,b,c$, `overlap_sq` identifies $21$ times the squared overlap modulus with the squared modulus of this numerator.
2. **The bound for unit local factors.** `unit_coordinates` gives $|a_0|^2+|a_1|^2=1$ for $a\in\mathbb C^2$ with $\|a\|=1$. For arbitrary complex $x,y,u,v$, `scalar_cs` gives $|xu+yv|^2\le(|x|^2+|y|^2)(|u|^2+|v|^2)$. Applying these identities and inequalities, `overlap_bound` states that for $a,b,c\in\mathbb C^2$ with $\|a\|=\|b\|=\|c\|=1$, and $A=|a_0|^2$, $B=|b_0|^2$,
   $21|\langle D,a\otimes b\otimes c\rangle|^2\le5A+5B+6AB$.
3. **Coordinates of any maximizer.** `basis_attains` gives the squared overlap $16/21$ for the fixed local factors $a=|0\rangle$, $b=|0\rangle$, $c=|1\rangle$. For $a,b,c\in\mathbb C^2$ satisfying `IsClosestProduct 4 a b c`—each factor is unit and its product has overlap at least that of every other product of unit factors—`closest_coordinates` states $a_1=b_1=c_0=0$ and $a_0b_0c_1\ne0$. Its proof compares with `basis_attains`; normalization gives $0\le A,B\le1$, and the bound forces $A=B=1$ and $|c_1|^2=1$.
4. **The subspace obstruction.** For any $v\in\mathbb C^8$ with $v\in\texttt{symQ}\,4$, `span_relation` states $v_{001}=2v_{010}$. The linear functional $v\mapsto v_{001}-2v_{010}$ vanishes on the four spanning vectors. For $a,b,c\in\mathbb C^2$ satisfying `IsClosestProduct 4 a b c`, `no_closest_in_span` combines this relation with `closest_coordinates` to conclude $a\otimes b\otimes c\notin\texttt{symQ}\,4$.
5. **Refutation.** `result : ¬ claim` applies the universal existence assertion to the positive real parameter $q=4$ and contradicts `no_closest_in_span`.

## Falsifier

The correspondence with the source is essential. The module's `dicke1` and `dicke2` have exactly the three-qubit coefficients above, its `symQ` is their full complex span together with the two endpoint vectors, and `prod` is the ordinary coordinatewise tensor product. `IsClosestProduct` requires unit local factors and compares the ordinary overlap modulus with every product of unit complex local factors. `claim` quantifies over every positive real $q$. Although the vector definitions accept all real inputs, the claim makes no assertion at $q\le0$.

The comparison is over all complex local factors, including their phases. Membership is in the full q-symmetric subspace. A different metric, different local normalization, or a deformed notion of product would define a different optimization problem. The explicit normalized comparison product $|001\rangle$ prevents the obstruction from relying on an empty comparison family.

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation.lean` (180 lines).

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Reuse.** The scalar Cauchy–Schwarz inequality uses `LowRankRays.cs_sq`; the unit-coordinate identity uses `DelayedRemoteControlDimensionWitness.unit_coordinates`.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation.lean.json`, statement `sha256:fdcc81646fed332347b9b408fed9edd7e61619eac349b40d1808b12d1ba228b6`.

Declaration statements:

- `result`: `sha256:a788a40aa96d498288474aa3f95e3b5dac2f3b49e5ec16805bb8ba41bd098ec2`;
- `claim`: `sha256:2b4142b047e05ad8af52218471e18a03c7c6dd8a7b0d59803d1c4548a4a6d2f1`.

## Triage

Tier 1: an explicit conjecture in the v3 e-print of a 2025 journal article, preregistered in issue #21970 before any Lean.
`theorem`; resolution `refuted`.

The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that for every real $q>0$ there exist unit $a,b,c\in\mathbb C^2$ whose product both maximizes the ordinary overlap modulus with `dicke1 q` among all products of unit local factors and belongs to `symQ q`.

**Computed, not formalized** (exact symbolic and rational arithmetic):

- *Three-qubit arithmetic.* Exact rational and symbolic arithmetic gives $[3]_4=21/4$, squared norm $21$ for $4|001\rangle+2|010\rangle+|100\rangle$, and squared overlap $16/21$ with $|001\rangle$. The functional $v_{001}-2v_{010}$ is zero on all four spanning vectors and equals $1$ on $|001\rangle$. The identity $16-(5A+5B+6AB)=5(1-A)+5(1-B)+6(1-AB)$ has zero symbolic residual. These are independent arithmetic checks of quantities used by the module.
- *Two-qubit observation, outside the Lean module.* The state at TeX l. 565 and the span at l. 571 give, with $r=\sqrt q>0$, $|D^1_2\rangle_q=(r|01\rangle+|10\rangle)/\sqrt{r^2+1}$ and $\mathrm{Sym}_q\mathcal H=\mathrm{span}_{\mathbb C}\{|00\rangle,r|01\rangle+|10\rangle,|11\rangle\}$. Exact symbolic multiplication of its coefficient matrix $M=\begin{pmatrix}0&r\\1&0\end{pmatrix}/\sqrt{r^2+1}$ gives $MM^*=\mathrm{diag}(r^2,1)/(r^2+1)$. The functional $L(v)=v_{01}-rv_{10}$ annihilates that span, while $L(|01\rangle)=1$ and $L(|10\rangle)=-r$. At $q=4$ the squared Schmidt coefficients are exactly $4/5$ and $1/5$; at $q=1/4$ they are $1/5$ and $4/5$. The symbolic gap identities used in the following argument were also checked exactly.

**Argued, not formalized**:

- *Mechanism at the formal counterexample.* For $a,b,c\in\mathbb C^2$ satisfying `IsClosestProduct 4 a b c`, `closest_coordinates` forces their product to be a nonzero multiple of $|001\rangle$; unit normalization makes the multiplier a phase. For every $v\in\texttt{symQ}\,4$, `span_relation` instead requires $v_{001}=2v_{010}$. Thus the coordinate concentration selected by ordinary overlap maximization is incompatible with the linked amplitudes required by q-symmetry. These are the helper statements used on the proof path; the displayed type of `result` itself is the negation stated above.
- *The two-qubit sentence.* For unit $a,b\in\mathbb C^2$, set $B=|b_0|^2\in[0,1]$. Cauchy–Schwarz bounds the squared numerator of the overlap by $r^2(1-B)+B$. When $r>1$, its gap from $r^2$ is $(r^2-1)B$, so equality forces $b_0=0$ and then $a_1=0$. The best product is therefore a phase times $|01\rangle$, attaining squared overlap $q/(q+1)$. When $0<r<1$, the gap from $1$ is $(1-r^2)(1-B)$, so equality forces $b_1=0$ and $a_0=0$: the best product is a phase times $|10\rangle$, attaining $1/(q+1)$. The computed functional values exclude every such maximizer from the q-symmetric span. Consequently the source's quoted two-qubit sentence at l. 1258 is false as stated for positive real $q\ne1$. This argument and its exact computation are outside the Lean module.
- *Missing metric compatibility.* The source defines $Q(\psi,\phi)=\langle\psi,C^{-1}(\tau)\phi\rangle$ at l. 982, with position-dependent local norms at l. 996. Rewriting an overlap using that metric does not preserve the ordinary unit constraints: under a local map $T$, an ordinary unit vector satisfies $\|T\phi\|^2=\langle\phi,T^*T\phi\rangle$, which need not be $1$ for a nonunitary $T$. Thus a transfer of a symmetric-state maximization argument must also transport the normalization constraints. A general replacement theorem using consistently deformed norms and overlaps remains open here.
- *Nearby statements that survive.* For $q>0$, the three-qubit endpoint q-Dicke states $|000\rangle$ and $|111\rangle$ are themselves normalized q-symmetric products. Their self-overlap is $1$, and Cauchy–Schwarz bounds every unit product overlap by $1$, so each has a q-symmetric closest product. For the two-qubit one-excitation state at $q=1$, the bound above is $1/2$ for the squared overlap; $|+\rangle\otimes|+\rangle$, with $|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$, attains it and belongs to the symmetric span. These observations do not classify the three-qubit problem for other positive $q$, or larger chains and other excitation numbers; those ranges remain open here.
- *Effect on the source.* The proposed restriction of the ordinary geometric optimization to q-symmetric products is invalid in the exhibited three-qubit case, and the two-qubit rationale is contradicted by the calculation above. The conjecture therefore cannot justify the proposed general analytic-entanglement families. This does not exclude analytic formulas obtained by other methods. The refutation supplies no assessment of the separate representation-theoretic results or metrological applications, and it does not verify or refute the numerical entanglement-degradation observation at l. 1258.

## ASSUMED-UNVERIFIED

The literature check is bounded by the searches recorded in #21970 and does not establish exhaustive worldwide novelty or priority. The reported searches of citing works and v1/v2, and the reported absence of prior repository records, were not independently reproduced. The older entanglement-entropy paper cited in that search was not independently read. The published journal text was not compared with v3; the source quotation and formulas here are from the downloaded v3 TeX, md5 `18fa3b609df74e7f0e866cc4ee871711`.

The statements under “Computed, not formalized” and “Argued, not formalized” are not additional formal conclusions of `result`; the cited private helper statements are already part of its proof. In particular, the two-qubit analysis, the metric-compatibility diagnosis, the endpoint and undeformed examples, and the consequences for proposed applications have no additional Lean declarations here. A classification for other parameters and a theorem for consistently deformed optimization remain open. The source's numerical evidence about entanglement degradation and its other applications were not reproduced.
