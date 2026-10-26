---
slug: muller-saniga-giorgetti-de-boutray-holweck-2022-linear-doily-odd-negative-lines
bibkey: mullersanigagiorgettideboutrayholweck2022doilies
doi: 10.1016/j.jocs.2022.101853
url: https://arxiv.org/abs/2206.03599v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity.result
---

# Every linear N-qubit doily has an odd number of negative lines

## Problem

A. Muller, M. Saniga, A. Giorgetti, H. de Boutray and F. Holweck, *Multi-qubit doilies: enumeration for all ranks and classification for ranks four and five*, arXiv:2206.03599v2 (J. Comput. Sci. 64, 101853, 2022), §5.4, “Specific behavior of linear doilies”, state:

> From our results on three-, four- and five-qubit cases it follows that a linear doily (a) always features an odd number of negative lines, and (b) does not share a perp-set with the distinguished quadric.

> We conjecture that Property (a) holds for any number of qubits $N \geq 2$, but we have not yet found of proof of it; we surmise that it has something to do with the fact that a linear doily is ``squeezed'' into a PG$(3,2)$, compared to a quadratic doily that enjoys more degrees of freedom being stretched out in a PG$(4,2)$.

These quotations are from `xiv-MSGDH2.tex`, lines 2255–2257 and 2259–2263, downloaded from the [v2 source](https://arxiv.org/src/2206.03599v2), MD5 `ba1ee66980eb180ebdcbe7fcd5d8a411`. Definitions and source locators are in [the literature note](../Library/QuantumContext/mullersanigagiorgettideboutrayholweck2022doilies.md).

Issue [#20146](https://github.com/the-omega-institute/trureturing/issues/20146) fixes the reading: for every $N\ge2$ and every four-dimensional subspace $U\le\mathbb F_2^{2N}$ with nondegenerate restricted symplectic form, an odd number of its isotropic triples $\{u,v,u+v\}$ have their three canonical, unsigned Pauli observables multiplying to $-I_{2^N}$. This is proved.

## Motivation

The paper enumerates linear and quadratic doilies and classifies their observable signatures and negative-line configurations for four and five qubits. Line signs enter its operator-based contextuality analysis. The conjecture asks whether the parity observed in the finite classifications is forced by linearity for every number of qubits; its settlement gives a uniform constraint on those configurations.

## Gap

The bounded literature check recorded in #20146 reports:

- The orchestrator read the v2 TeX, which retains the conjecture; arXiv lists v1 and v2.
- The orchestrator found 12 citing works through Semantic Scholar and scanned the TeX sources of arXiv:2410.14463, 2305.10225, 2407.02928, 2609.19862, 2602.08410, 2610.26465 and 2403.09512, finding no proof of this parity statement. The reported contextuality-degree invariance result in 2410.14463 concerns a different quantity.
- The search contributor reported screening the remaining citing works, Muller's thesis (HAL tel-05351702), MathDB and `google-deepmind/formal-conjectures`, without finding a resolution.
- The orchestrator reported no existing record of this problem on `dev`; the Lau doily dossier concerns a nonlocal game.

`not-found-in-searched-scope`. The source quotation and checksum are independently reproduced here; the external literature screening is attributed to its recorded authors.

## Route

The proof uses the multiplication phases of the literal Pauli matrices.

1. **Coordinates.** A symplectic basis $g_0,\ldots,g_3$ identifies $U$ with $\mathbb F_2^4$ carrying the form $a_0b_1+a_1b_0+a_2b_3+a_3b_2$. The fifteen fixed isotropic triples in this coordinate space map bijectively to `lines U`.
2. **Local multiplication.** For binary pairs $p=(x,z)$ and $q=(y,t)$, with bars denoting their representatives in $\{0,1\}$, put $e(p,q)=\bar x\bar z+\bar y\bar t-\overline{x+y}\,\overline{z+t}+2\bar z\bar y$ in $\mathbb Z/4\mathbb Z$. The canonical matrices satisfy $P(p)P(q)=i^{e(p,q)}P(p+q)$. Tensor products give the global phase.
3. **Total phase.** For the module's fifteen ordered coordinate representatives `modelPair`, denoted $(a_k,b_k)$ and any four single-qubit labels $w_0,\ldots,w_3$, the sum of $e(\sum_i(a_k)_iw_i,\sum_i(b_k)_iw_i)$ over $k$ is $2\overline{(w_0)_x(w_1)_z+(w_0)_z(w_1)_x}$ modulo four. The Lean proof checks this fixed identity over all 256 assignments. At each qubit take $w_i$ to be the local label of $g_i$. Multiplying over qubits makes the total line phase $(-1)^{B(g_0,g_1)}=-1$.
4. **Matrix signs and parity.** On an isotropic triple the observables commute, and their product is its phase times the identity, independently of list order. Each phase is $+1$ or $-1$. Their product is $-1$, so an odd number of the fifteen lines belong to `negativeLines U`.

## Falsifier

A mismatch in the subspace, the sign convention or the counted lines would prevent the result from settling the conjecture. The definitions make these choices explicit:

- `IsLinearDoily U` requires binary dimension four and zero radical for $B(u,v)=\sum_j(x_jt_j+z_jy_j)$, where $u=(x,z)$ and $v=(y,t)$. A source linear doily spans a projective three-space, so its fifteen points exhaust the nonzero vectors of a binary four-space. A nonzero radical point would commute with all fourteen other points, whereas a doily point has six collinear neighbours. Conversely a nondegenerate binary four-space carries $\mathcal W(3,2)$, the doily. This source-to-definition correspondence is a geometric argument, not a separate theorem of `result`.
- `canonicalLabel` maps $(0,0),(1,0),(0,1),(1,1)$ to $I,X,Z,Y$, with $Y=iXZ$, and `observable` takes their literal tensor product. The paper's coordinates swap $X$ and $Z$ (TeX lines 288–295); exchanging the two coordinates at every qubit identifies the conventions and preserves the symplectic form and observables.
- `lines U` consists of three-element subsets of nonzero vectors in $U$, closed under addition of distinct elements, with zero pairwise symplectic pairing. `negativeLines U` retains exactly those whose actual matrix product is minus the identity. The proof supplies the bijection with the fifteen coordinate triples; the conclusion does not assume their signs or parity.

## Evidence

The canonical source is `D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity.lean` (692 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity.lean.json`, statement `sha256:69cd69f00ccac0f329647bd976d39b9c628f781963bb3443ec0029276db597de`.

Declaration statements:

- `result`: `sha256:60c7c078aababdfb9af0e37c5eb16ee41f323095b747456b052a9c326e7c9588`;
- `claim`: `sha256:a4ee61fcd24e8ed1e400b44b6544a0e57a13dde15700dabc8ad7820c91e132a0`.

## Triage

Tier 1 conjecture of a 2022 paper, preregistered in issue #20146 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $N\ge2$ and every subspace $U\le(\mathbb F_2^2)^N$ of binary dimension four whose restricted symplectic form has zero radical, the cardinality of `negativeLines U` is odd, where a negative line is an isotropic triple whose three canonical unsigned Pauli tensor products multiply to $-I_{2^N}$.

**Computed, not formalized** (exact Pauli-matrix arithmetic and enumeration):

- At $N=2$ the single four-space has three negative triples: $\{XX,YY,ZZ\}$, $\{XY,YZ,ZX\}$ and $\{XZ,YX,ZY\}$.
- At $N=3$, enumeration of all 651 binary four-subspaces found 336 with nondegenerate restricted form, each with fifteen isotropic triples. The negative-line counts were three for 147 subspaces, five for 162 and seven for 27. No even count was observed in this tested family.
- Replacing $XI$ by $-XI$ in the two-qubit configuration changes its three incident line signs and changes the negative-line count from three to six.
- The four-dimensional space of $Z$-only words at $N=4$ has fifteen points, 35 isotropic triples and zero negative lines.

**Argued, not formalized.**

- *Decisive mechanism and scope.* The local exponent identity controls the product of all line signs, without requiring the individual signs to be preserved under an embedding. The same 256 local assignments suffice at every qubit; taking their product introduces no bound on $N$. The parity conclusion does not determine a unique negative-line count, as the computed three-qubit examples illustrate.
- *Canonical signs matter.* Replacing each point operator $P(v)$ by $\varepsilon(v)P(v)$ multiplies each line sign by the three corresponding $\varepsilon$ factors. Each doily point belongs to three lines, so the total line-sign product changes by $\prod_{v\ne0}\varepsilon(v)^3=\prod_{v\ne0}\varepsilon(v)$. Consequently an even number of point sign changes preserves parity, and an odd number reverses it. The theorem concerns the canonical unsigned observables; arbitrary signed assignments need not have odd parity.
- *Nondegeneracy matters.* In the $Z$-only four-space, $B$ vanishes identically and $P(u)P(v)=P(u+v)$, so every triple product is $+I$. All pairs of distinct nonzero vectors generate isotropic triples, giving $15\cdot14/6=35$ lines. Thus dimension four alone would not suffice; this space is outside `IsLinearDoily`.
- *Identity padding.* Appending identity factors sends $P(v)$ to $P(v)\otimes I$, preserves $B$, and gives a bijection of points and lines onto the embedded four-space, preserving each line product. It therefore preserves the full negative-line configuration. In particular the two-qubit example yields a three-negative-line example for every $N\ge2$. No optimal lower bound or complete list of achievable counts for arbitrary $N$ is established by `result`.
- *Effect on the source and neighbouring questions.* Property (a) of §5.4 has the asserted all-$N$ scope. The counting theorem in §3.1 and the finite classifications in §5 have their own arguments; their numerical values are not certified by this module. Property (b) has a separate geometric proof in the source (TeX lines 2263–2276). For the polar pairs of four-qubit linear doilies discussed in the conclusion (lines 2400–2420), applying the parity statement to each member restricts both negative-line counts to be odd; equality of those counts, compatible signatures and pair multiplicities remain outside this settlement. Quadratic doilies and the source's contextuality-degree proposition in §2.3 are also outside the theorem's scope.

## ASSUMED-UNVERIFIED

The bounded literature check in #20146 does not establish exhaustive worldwide novelty or priority. The citing-work scans, thesis and database screening were not independently reproduced; the distinctions between orchestrator readings and search-contributor reports in that issue remain material. The issue's random matrix checks (180 examples), reported 20,000 random embeddings and reported enumeration of 91,392 four-qubit linear doilies were not reproduced here and are not used as proof.

The statements labelled “Computed, not formalized” and “Argued, not formalized”, including the geometric correspondence to the source's definition, sign-change rule and identity-padding consequence, are not additional conclusions of `result`. The source's counting, classification, contextuality-degree and perp-set results are not independently formalized or validated by this dossier. General realizability of specified negative-line configurations and the polar-pair classification are not settled here.
