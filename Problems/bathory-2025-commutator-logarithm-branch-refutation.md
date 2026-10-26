---
slug: bathory-2025-commutator-logarithm-branch-refutation
bibkey: bathory2025commutator
doi: 10.1137/25M1760209
url: https://arxiv.org/abs/2505.07987v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/CommutatorLogarithmBranchRefutation.result
---

# The complex matrix exponential does not determine the halved commutator

## Problem

M. Bathory, *Commutator calculus and symbolic differentiation of matrix functions* (2025 preprint; SIAM J. Matrix Anal. Appl., 2026), arXiv:2505.07987v3, Conjecture 3.7. The following is the verbatim TeX text of `cc_arxiv_1_.tex`, line 506 (conjecture environment at lines 505–507), MD5 `3f5e6f983ebd4bc8e0036ae4a4b880db`:

> With a~suitable generalization of Definition~\ref{Def}, all identities of Theorem~\ref{Tform}, Lemma~\ref{Had}, and Corollaries~\ref{corpow},~\ref{Cor} (except \eqref{eq1}, \eqref{eq2}) continue to hold for every $\mathbf{G}\in\mathbb{C}^{d\times d}$ and for any $\mathbf{A}\in\mathbb{C}^{d\times d}$ such that $\log\mathbf{A}$ exists.

The references in this quotation denote Definition 2.1, Theorem 3.2, Lemma 3.4, Corollaries 3.5 and 3.6, and the exceptions (3.55) and (3.56). The source and operator definitions are also documented in [the literature note](../Library/Eigenstructure/bathory2025commutator.md).

For a matrix $G$, write $L_G(X)=GX$, $R_G(X)=XG$, and $\operatorname{ad}_G=(L_G-R_G)/2$, following Eq. (1.1), TeX line 38. Lemma 3.4 assumes $G\in\mathbb R^{d\times d}_{\rm sym}$ and $A=e^G$; its Eq. (3.42), at TeX line 385, expresses $\operatorname{ad}_G$ as $(\log L_A-\log R_A)/2$.

Issue [#20790](https://github.com/the-omega-institute/trureturing/issues/20790) fixes the complex extension to be settled. Put $M=\mathbb C^{2\times2}$. The claim is that there exist two functions $\Lambda_L,\Lambda_R:M\to\operatorname{End}_{\mathbb C}(M)$ such that, for every $G\in M$,

$\displaystyle \frac12(L_G-R_G)=\frac12\bigl(\Lambda_L(e^G)-\Lambda_R(e^G)\bigr).$

Both operator-valued functions depend only on $A=e^G$. No continuity, analyticity, or logarithm identities are imposed on them. This reading of the conjecture is refuted.

## Motivation

Bathory's calculus expresses derivatives of matrix functions through multiplication, anticommutator and commutator operators. Its applications include logarithmic strain, objective rates and viscoelastic models. Conjecture 3.7 proposes extending several identities beyond real symmetric matrices. Recovering the commutator from the exponential is one required identity in that proposed extension; it tests whether the exponential retains the information those logarithm operators would need.

## Gap

Issue #20790 records the bounded literature check:

- the v3 source retains Conjecture 3.7; this is confirmed by the source text quoted above;
- the orchestrator reports that DOI `10.1137/25M1760209` resolves to SIAM J. Matrix Anal. Appl.;
- the orchestrator reports zero citing works in OpenAlex record `W4417151775`;
- the orchestrator reports no existing repository record on `dev` from an issue search for the arXiv identifier.

No settlement was found in that recorded search scope: `not-found-in-searched-scope`. The source reading is independent evidence for the quotation, not an exhaustive literature check.

## Route

1. **A shared exponential.** Take $G_0=0$ and $G_1=\operatorname{diag}(0,2\pi i)$. The identities for diagonal matrix exponentials and $e^{2\pi i}=1$ give $e^{G_0}=e^{G_1}=I$.
2. **A forced equality.** Applying the claimed identity at these two matrices makes both right sides equal to $(\Lambda_L(I)-\Lambda_R(I))/2$. Consequently their halved commutator operators would agree.
3. **A separating entry.** Let $E_{01}$ have entry one at row 0, column 1, and zero elsewhere, using Lean's zero-based indexing. Then $G_1E_{01}=0$, $E_{01}G_1=2\pi iE_{01}$, and hence $\operatorname{ad}_{G_1}(E_{01})=-\pi iE_{01}$, whereas $\operatorname{ad}_{G_0}(E_{01})=0$. Equality of the row-0, column-1 entries contradicts $\pi>0$ and $i\ne0$.

## Falsifier

The source-to-formal bridge would fail if the proposed logarithm operators were allowed to depend on a selected logarithm $G$ or on an additional branch label, rather than only on $A$. The compiled `claim` expressly requires functions of $A$ alone and quantifies over every complex two-by-two $G$. It does not formalize a multivalued logarithm relation or a restriction to one chosen lift of each exponential.

The factor one half agrees with the source's commutator convention. `LinearMap.mulLeft` and `LinearMap.mulRight` act on the full complex matrix space by $X\mapsto GX$ and $X\mapsto XG$; the test matrix is not restricted to be symmetric or Hermitian. `NormedSpace.exp` is the matrix exponential. The counterexample uses $A=I$, which has a logarithm, so the source's existence condition on $\log A$ does not exclude it. The source's real symmetric hypothesis does exclude $G_1$.

## Evidence

The canonical source is `D5/S3/Quantum/Matrix/CommutatorLogarithmBranchRefutation.lean` (45 lines).

- **Proof.** It proves `result : ¬ claim`.
- **Reuse.** The proof uses mathlib's `Matrix.exp_diagonal`, the complex exponential identity at $2\pi i$, and entrywise evaluation of the multiplication linear maps.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Matrix/CommutatorLogarithmBranchRefutation.lean.json`, statement `sha256:2feaca45603ec40157876b77aa80e180880c47aa0f587dff09f3f577250eef58`.

Declaration statements:

- `result`: `sha256:211d50f2fb1c1bab7e68cf3d9e77e1ef21aa082f7a01559732442d14efdf43f6`;
- `claim`: `sha256:13bb6af6d3720ff6c71945700ed42729440d92dc97c7bd636e590e85bc1f4a36`.

## Triage

Tier 1 conjecture of a 2025 preprint, published in 2026, preregistered in issue #20790 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| `result` | bind-only | none: diagonal exponential identities and entrywise evaluation of existing multiplication maps | open-problem-resolution |
| `claim` | bind-only | none | definition used by `result` |

The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** there do not exist two functions from complex two-by-two matrices to complex-linear endomorphisms of that matrix space whose half-difference at $e^G$ equals $(L_G-R_G)/2$ for every complex two-by-two matrix $G$.

**Computed, not formalized** (by hand from the definitions):

- At $G_1=\operatorname{diag}(0,2\pi i)$, the exponential is $I$, and the halved commutator and anticommutator applied to $E_{01}$ are $-\pi iE_{01}$ and $\pi iE_{01}$, respectively. These values agree with the counterexample calculations in #20790.
- On this test vector, $\sinh(\operatorname{ad}_{G_1})E_{01}=\sinh(-\pi i)E_{01}=0$, agreeing with $\operatorname{ad}_I E_{01}$. This is only a calculation on one input.
- The first identity of Lemma 3.4 (TeX line 380) requires its own power convention in a complex extension. With principal powers of $A=I$, $p=0$ and $q=1/2$, its left side $L_{A^p}R_{A^q}$ gives entry $1$ on $E_{01}$, while $e^{(p+q)\operatorname{ac}_{G_1}}e^{(p-q)\operatorname{ad}_{G_1}}$ gives entry $-1$. So under this interpretation Eq. (3.37) also fails at the pair, as recorded in #20790. It does not settle other branch conventions or the other identities.

**Argued, not formalized**

- *Mechanism and the missing structure.* The final step of the source's proof of Lemma 3.4 writes $G=\log A$ (TeX line 405). For complex matrices, $A=e^G$ alone does not license that equality for a fixed logarithm. More precisely, two matrices $G,H\in M$ have the same halved commutator exactly when $G-H=cI$ for some $c\in\mathbb C$: equality says that $G-H$ commutes with every matrix; commuting with $E_{00}$ and $E_{11}$ forces it to be diagonal, and commuting with $E_{01}$ forces its two diagonal entries to agree. Conversely, scalar matrices commute with everything. Recovering the commutator therefore permits scalar lift ambiguity, but the exhibited exponential fibre contains nonscalar ambiguity.
- *A restricted repair.* If a function $H$ is supplied with $e^{H(A)}=A$ on an allowed domain, restrict the generators to those satisfying $G-H(e^G)=cI$. Setting $\Lambda_L(A)=L_{H(A)}$ and $\Lambda_R(A)=R_{H(A)}$ then gives the commutator identity, because the scalar difference contributes zero. This is a conditional repair of this identity only; it neither constructs such a branch on a specified complex domain nor restores the full conjecture.
- *The source's symmetric case.* For a real symmetric $G=Q\operatorname{diag}(g_j)Q^{\mathsf T}$, the numbers $g_j$ are real and $e^{g_j}>0$. The real logarithm returns each $g_j$. In the basis $QE_{ij}Q^{\mathsf T}$, the logarithms of $L_{e^G}$ and $R_{e^G}$ therefore act by $g_i$ and $g_j$, giving their half-difference $(g_i-g_j)/2$. This explains why the stated real symmetric identity avoids the obstruction.
- *A neighbouring obstruction.* The same pair also prevents an $A$-only universal version of Eq. (3.41), the anticommutator identity: its right side would be the same half-sum of two maps at $I$, while the left sides send $E_{01}$ to $0$ and $\pi iE_{01}$. This consequence is not another Lean settlement.
- *Effect on the paper.* Conjecture 3.7's simultaneous extension of Theorem 3.2, Lemma 3.4 and Corollaries 3.5–3.6 cannot include Eq. (3.42) with the registered $A$-only, all-$G$ reading. Those results in their stated real symmetric setting are not refuted. The source's logarithm-derivative derivation explicitly invokes Eq. (3.42) at TeX lines 990–995; extending that derivation requires compatible logarithm choices rather than identifying a fixed $\log A$ with every generator of $A$. The individual complex derivative identities and the alternative calculus constructions discussed at line 509 are not settled by `result`.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The OpenAlex count, the DOI-resolution reading and the repository-search reading are the orchestrator's reports in #20790 and were not independently reproduced. The issue's seat-reported connection to `AnswerabilityCriterion` was not independently checked and is not used as formal evidence.

Everything under "Computed, not formalized" and "Argued, not formalized" lies outside the statement of `result`. In particular, no branch-domain construction, general power identity, anticommutator refutation, or complex derivative extension is claimed as formalized. The preregistration's blanket assertion about the remaining Lemma 3.4 identities is not adopted; the principal-power test above gives a different reading, and branch-dependent alternatives remain open. The relationship between a future branch-labelled or multivalued generalization and the source's phrase "suitable generalization" remains an interpretive boundary, not a further conclusion of the Lean theorem.
