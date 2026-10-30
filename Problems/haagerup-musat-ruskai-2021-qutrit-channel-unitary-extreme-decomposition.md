---
slug: haagerup-musat-ruskai-2021-qutrit-channel-unitary-extreme-decomposition
bibkey: haagerupmusatruskai2021extreme
doi: 10.1007/s00023-021-01071-y
url: https://arxiv.org/abs/2006.03414v4
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/QutritChannelUnitaryExtremeDecomposition.result
---

# Every equal-modulus HMR qutrit channel has a unitary and doubly extreme decomposition

## Problem

U. Haagerup, M. Musat and M. B. Ruskai, *Extreme Points and Factorizability for New Classes of Unital Quantum Channels*, arXiv:2006.03414v4 (Annales Henri Poincaré 22, 3455–3496, 2021), §2.3.1, “Non-extreme cases”, `HMR2021J.tex`, lines 387–390:

> It seems reasonable to conjecture that,
> whenever  $|\alpha | = |\beta| = \1rt2$, the channel $\Phi_{\alpha,\beta} $ is a convex combination of a
> unitary conjugation and a map with Choi-rank $3$ which is extreme in both the UCP and CPT maps.
> However, one would need a different unitary transformation relating $\{ A_k \} $ to $\{ X_k \} $.

The source macro `\1rt2` means $1/\sqrt2$ (line 56). For the standard basis of $\mathbb C^3$, the four operators of Theorem `thm:UCPT` (lines 280–290) are

$A_1=\alpha|e_1\rangle\langle e_1|+|e_2\rangle\langle e_3|$, $A_2=\beta|e_1\rangle\langle e_3|+|e_3\rangle\langle e_2|$,

$A_3=-|e_1\rangle\langle e_2|-\overline\beta|e_3\rangle\langle e_1|$, $A_4=|e_2\rangle\langle e_1|+\overline\alpha|e_3\rangle\langle e_3|$,

and $\Phi_{\alpha,\beta}(\rho)=\tfrac12\sum_{k=1}^4 A_k^*\rho A_k$. Here UCP means unital completely positive, CPT means completely positive and trace preserving, and UCPT means both. The definitions and source locators are in [the literature note](../Library/Eigenstructure/haagerupmusatruskai2021extreme.md).

Issue [#22743](https://github.com/the-omega-institute/trureturing/issues/22743) fixes the statement: for every $\alpha,\beta\in\mathbb C$ with $|\alpha|=|\beta|=1/\sqrt2$, there exist a unitary $U\in M_3(\mathbb C)$, a real $\lambda\in[0,1]$, and a complex linear map $\Psi:M_3(\mathbb C)\to M_3(\mathbb C)$ such that $\Psi$ is completely positive, unital and trace preserving, its Choi matrix has rank $3$, it is separately extreme in the UCP and CPT sets under real convex combinations, and

$\Phi_{\alpha,\beta}(\rho)=\lambda U^*\rho U+(1-\lambda)\Psi(\rho)$

for every complex matrix $\rho\in M_3(\mathbb C)$. This is proved.

## Motivation

The paper distinguishes extremality in the intersection UCPT from extremality in either of the larger UCP and CPT sets. Its equal-modulus example decomposes into a unitary conjugation and a channel extreme in both larger sets. The conjecture asks whether this structure survives arbitrary phases of both parameters, rather than only the positive real example and the special phase relations discussed in the source.

## Gap

The literature check recorded in #22743 has the following bounded scope:

- The arXiv v4 source retains the conjecture; the conjecture and its positive real base case are directly checked in `HMR2021J.tex`, lines 366–390.
- The search contributor reports six citing works in OpenAlex and a union of nine arXiv papers from Semantic Scholar and OpenCitations, screened in full text without finding a settlement: 2111.13705, 2210.03449, 2211.02401, 2305.05795, 2309.03108, 2412.10041, 2507.16637, 2512.00432 and 2603.17010.
- The same contributor reports no match in MathDB or formal-conjectures. The orchestrator reports no matching repository dossier or Library note; issue #18583 concerns the different tensor-product extremality question in arXiv:2305.05795.

`not-found-in-searched-scope`.

## Route

Write $C(\varphi)$ for the unnormalized Choi matrix used by the module, and put $a=1/\sqrt2$.

1. **The explicit base channel.** The definitions `baseUnitary` and `baseKraus` give $U_0=2X_2$ and $(Y_1,Y_2,Y_3)=\tfrac2{\sqrt3}(X_1,X_3,X_4)$ for the source's matrices at $\alpha=\beta=a$ (lines 370–379). Set $\Psi_0(\rho)=\sum_{i=1}^3Y_i^*\rho Y_i$. The lemma `base_decomposition` proves $U_0$ unitary and $\Phi_{a,a}(\rho)=\tfrac14U_0^*\rho U_0+\tfrac34\Psi_0(\rho)$ for every $\rho$. The closed lemmas `base_unital` and `base_trace` give $\sum_iY_i^*Y_i=I$ and $\sum_iY_iY_i^*=I$; `base_left_independent` and `base_right_independent` prove complex linear independence of the respective nine-product families using dual coordinate identities.
2. **The extremality mechanism.** For any three matrices $y_i\in M_3(\mathbb C)$, let $\Psi_y(\rho)=\sum_i y_i^*\rho y_i$. Given a completely positive $\theta$, a real $t>0$, and $C(\Psi_y)-tC(\theta)$ positive semidefinite, `choi_range_lift` gives a matrix $H$ with $\theta(\rho)=\sum_{i,j}H_{ij}y_i^*\rho y_j$ for every $\rho$. For such a three-matrix family, `extreme_ucp_of_independent` assumes $\sum_i y_i^*y_i=I$ and complex linear independence of all nine $y_i^*y_j$, and concludes UCP extremality of $\Psi_y$. The lemma `extreme_cpt_of_independent` assumes $\sum_i y_i y_i^*=I$ and complex linear independence of all nine $y_i y_j^*$, and concludes CPT extremality. These normalizations force the coefficient matrix to be the identity in the respective convex-decomposition arguments. Independently of either normalization, `choi_rank_of_independent` assumes complex linear independence of the nine $y_i^*y_j$ and proves $\operatorname{rank}C(\Psi_y)=3$.
3. **Removing both phases.** Under precisely $|\alpha|=|\beta|=a$, `phase_parameters` supplies unit-modulus $r,s\in\mathbb C$ with $rs^2=\sqrt2\alpha$ and $r^2/s=\sqrt2\beta$. Its witness construction sets $u=\sqrt2\alpha$, $v=\sqrt2\beta$, chooses $r^5=uv^2$, and takes $s=r^2/v$; both $u$ and $v$ have modulus one, so the division is legitimate. Under the same two modulus hypotheses, `phase_reduction` proves that $D=\operatorname{diag}(r,1,r^{-1})$ and $E=\operatorname{diag}(s,1,s^{-1})$ are unitary and that $\Phi_{\alpha,\beta}(\rho)=E^*\Phi_{a,a}(D^*\rho D)E$ for every $\rho$.
4. **Transporting the decomposition.** The lemma `transport` takes three unitary matrices $D,E,U\in M_3(\mathbb C)$, complex linear maps $\varphi,\psi$ on $M_3(\mathbb C)$, and the hypotheses that $\psi$ is completely positive, unital, trace preserving, of Choi rank $3$, separately extreme in the UCP and CPT sets over $\mathbb R$, and $\varphi(\rho)=\tfrac14U^*\rho U+\tfrac34\psi(\rho)$ for every $\rho$. It supplies the corresponding decomposition of $\rho\mapsto E^*\varphi(D^*\rho D)E$, with unitary $DUE$ and remainder $\rho\mapsto E^*\psi(D^*\rho D)E$ retaining all those properties. Applying it to the base channel and the phases above gives the witnesses in `result`. The proof chooses $\lambda=1/4$; the exported proposition requires only $0\le\lambda\le1$.

## Falsifier

A proof of extremality only in UCPT, or a decomposition only for real parameters or density matrices, would not settle the stated conjecture. The module instead uses the source's four operators in their stated order and its adjoint-on-the-left convention; its conclusion covers every complex matrix $\rho$ and all complex phases satisfying the two norm equalities. `IsUnital` means exactly $\Psi(I)=I$, trace preservation quantifies over every matrix, and complete positivity quantifies over every finite matrix amplification. The two `Set.extremePoints ℝ` memberships concern the full UCP and CPT sets separately. Choi rank is the natural-valued matrix rank, not merely the number of displayed Kraus operators.

## Evidence

The canonical source is `D5/S3/Quantum/QuantumChannels/QutritChannelUnitaryExtremeDecomposition.lean`.

- **Proof.** It proves `result`, whose type is the universal existential decomposition stated above.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/QuantumChannels/QutritChannelUnitaryExtremeDecomposition.lean.json`.

Declaration statements:

- `result`: `sha256:67059671c3aa36d6e4296fd49c87c7ed774a13ba326e3c79cc22b0ec1bbcf17b`.

## Triage

Tier 1 conjecture of a 2021 Annales Henri Poincaré paper, preregistered in issue #22743 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $\alpha,\beta\in\mathbb C$ of norm $1/\sqrt2$, there exist a unitary $U\in M_3(\mathbb C)$, a real $\lambda\in[0,1]$, and a completely positive, unital, trace-preserving complex linear map $\Psi$ on $M_3(\mathbb C)$ of Choi rank $3$, separately extreme in the UCP and CPT sets over $\mathbb R$, such that $\Phi_{\alpha,\beta}(\rho)=\lambda U^*\rho U+(1-\lambda)\Psi(\rho)$ for every $\rho\in M_3(\mathbb C)$.

**Computed, not formalized:** numerical checks by the orchestrator of the base-case decomposition and of the phase identities for random equal-modulus pairs agreed with the formal statements.

**Argued, not formalized.**

- *Choi-rank sharpness.* For every allowed parameter pair, the four source operators are linearly independent: the entries $(2,3)$, $(3,2)$, $(1,2)$ and $(2,1)$ respectively recover their four coefficients, with a minus sign for the third. Their vectorized adjoints therefore give a Choi matrix of rank $4$. Since a unitary conjugation has Choi rank $1$, rank subadditivity in any decomposition of the stated form gives $4\le1+\operatorname{rank}C(\Psi)$. Thus a rank-three remainder is the smallest possible.
- *The weight is sharp.* For the same equal-modulus parameters, those four vectorized adjoints have pairwise disjoint supports and squared norms $3/2$. Consequently $C(\Phi_{\alpha,\beta})=\tfrac34P$, where $P$ is the orthogonal projection onto their four-dimensional span. If $w$ is the vectorized adjoint of a unitary, then $\|w\|^2=3$. A convex decomposition with a completely positive remainder gives $\lambda ww^*\le\tfrac34P$; evaluating on $w$ gives $9\lambda\le\tfrac34\langle w,Pw\rangle\le9/4$, hence $\lambda\le1/4$. The witness construction in `result` attains this bound. In fact, a rank-three remainder forces $\lambda=1/4$: $\lambda=0$ leaves rank $4$, while for $\lambda>0$ positivity forces $w$ into the range of $P$, and the four eigenvalues there of $\tfrac34P-\lambda ww^*$ are $3/4$ three times and $3/4-3\lambda$ once. These sharpness assertions are not part of the exported theorem statement.
- *Scope and neighbouring questions.* The phase-reduction lemma in the Route applies to every complex phase pair under exactly the two norm equalities, so no additional phase relation is needed. The argument supplies neither a classification of the possible unitaries and remainder maps nor an extension to unequal moduli or higher dimensions; those questions remain open here.
- *Effect on the source.* The conjectural extension in “Non-extreme cases” is settled for its entire stated family. The adjacent entanglement-of-formation bound in lines 393–442 is derived from the original four Kraus operators, without assuming this conjecture; this settlement does not certify that bound or its optimality. The source's generic-modulus extremality and factorizability theorem is a separate result, not a consequence supplied by `result`. No further theorem conditional on the equal-modulus conjecture is identified in the checked source passages and references.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The citation counts, nine-paper full-text screening, MathDB and formal-conjectures searches, and repository searches are readings attributed to the contributors in #22743 and are not independently reproduced. The numerical checks reported there are also not independently reproduced and imply nothing about untested cases. The source quotation and definitions are checked against the v4 TeX, and the DOI, title, authors and journal locator agree with Crossref; the published journal text is not independently compared with the arXiv text. The correspondence between source notation and the Lean definitions is a reading of those definitions, not a formal theorem about the source document. The sharpness arguments, interpretation of the phase mechanism, and discussion of consequences for other source statements are not formalized. Classification or uniqueness of the decomposition, extensions to unequal moduli or higher dimensions, the source's other conjectures, its factorizability results, and entanglement-of-formation bounds are not settled by this module.
