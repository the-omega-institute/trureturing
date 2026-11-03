---
slug: graffeo-gubbiotti-2024-nambu-kahan-cremona-decomposition
bibkey: graffeogubbiotti2024cremona
doi: 10.1007/s00023-023-01339-5
url: https://arxiv.org/abs/2301.09129v2
triage: theorem
motivation_gids:
  - D5/S3/FluidDynamics/Solitons/NambuKahanCremonaDecomposition.result
---

# The generic quadratic Nambu KHK map has a Cremona decomposition

## Problem

M. Graffeo and G. Gubbiotti study the Kahan–Hirota–Kimura (KHK) discretisation of the quadratic three-dimensional Nambu system
$ \dot{x}=\nabla H_1(x)\mathbin{\times}\nabla H_2(x),\qquad H_i(x)=x^{\mathsf T}A_i x. $
In Remark 7.7 of *Growth and Integrability of Some Birational Maps in Dimension Three*, they write:

> “We conjecture that, up to conjugation by a projectivity, the map $\Phi_{h}^{(N)}$ is of type (A)-(i), i.e. it exists an analogue of Lemma 2.6 for the map $\Phi_{h}^{(N)}$.”

This is quoted from `GG_cremona_v1_clean.tex`, lines 3209–3211, Remark `ex:celledoni`; the same remark says that a complete proof is left for further research.

The Lean module defines, for $X:\mathrm{Fin}\,4\to\mathbb C$, the polarised matrix `nambuLinearPart`, the homogeneous KHK matrix
$ K_{A,B,h}(X)=X(3)I_3-2h\,\mathrm{nambuLinearPart}(A,B)(X\mathbin{\circ}\mathrm{Fin.castSucc}), $
the homogeneous lift
$ \mathrm{kahan}(A,B,h,X)  =\mathrm{Fin.snoc}\bigl(\operatorname{adj}(K_{A,B,h}(X))\,\mathrm{mulVec}\,    (X\mathbin{\circ}\mathrm{Fin.castSucc}),\det K_{A,B,h}(X)\bigr), $
and
$ \mathrm{cremona}(X)= \bigl(X(1)X(2)X(3),\,X(0)X(2)X(3),\,X(0)X(1)X(3),\,X(0)X(1)X(2)\bigr). $
Its `claim` states that for every real $3\times3$ matrices $A,B$ with `A.PosDef` and `B.PosDef`, with
$ \forall t:\mathbb R,\quad 2\le \operatorname{rank}(B-tA), $
and every $h:\mathbb R$ with $0<h$, there are complex matrices $l_1,l_2:\mathrm{Matrix}(\mathrm{Fin}\,4)(\mathrm{Fin}\,4)\mathbb C$ such that `IsUnit l₁.det`, `IsUnit l₂.det`, and, for every $X:\mathrm{Fin}\,4\to\mathbb C$,
$ \mathrm{kahan}(A,B,h,X)  =l_2\,\mathrm{mulVec}\,    \mathrm{cremona}(l_1\,\mathrm{mulVec}\,X). $
The declaration `result` has type `claim`.

## Motivation

The source paper identifies the Euler top as the diagonal special case of these Nambu systems and proves in its Lemma 2.6 that the Euler-top KHK map is a composition of two projectivities and the standard cubic Cremona map. A decomposition of the general quadratic Nambu lift gives the same projective structure on the simple-pencil range encoded by the rank hypothesis above. It also supplies the structural form to which the paper’s type (A)-(i) analysis could be applied, while leaving those further applications as separate statements.

## Gap

Remark 7.7 supplied computational evidence for the Nambu decomposition but no complete proof. The formal gap is to reduce a positive-definite pair with a simple pencil to an Euler-top normal form, transport the KHK lift through that change of coordinates, and prove the Euler-top Cremona identity with explicit linear factors.

The bounded search recorded in issue [#26039](https://github.com/the-omega-institute/trureturing/issues/26039) reported no prior settlement of this Nambu decomposition in the checked literature and repository scope. That search is not an exhaustive novelty or priority result.

## Route

1. **Whitening (`whitening`).** For matrices $A,B$ and hypotheses `hA : A.PosDef`, `hB : B.PosDef`, and `hrank : \forall t:\mathbb R,\ 2\le(B-t\mathbin{\bullet}A).rank`, the lemma returns a real $P$ with `IsUnit P.det`, a function $\mu:\mathrm{Fin}\,3\to\mathbb R$, the identities
   $    P^{\mathsf T}AP=1,\qquad P^{\mathsf T}BP=\operatorname{diagonal}(\mu),    $
   and $\mu(i)\ne\mu(j)$ whenever $i\ne j$. The rank condition is therefore used exactly to obtain pairwise distinct diagonal coefficients.

2. **Covariance (`covariance`).** For arbitrary real $A,B,h$, real $P,\mu$, and hypotheses `IsUnit P.det`, $P^{\mathsf T}AP=1$, and $P^{\mathsf T}BP=\operatorname{diagonal}(\mu)$, the lemma proves for every complex $Z:\mathrm{Fin}\,4\to\mathbb C$ that
   $    \mathrm{kahan}(A,B,h,\mathrm{liftP}(P)\,\mathrm{mulVec}\,Z)    =\mathrm{liftP}(P)\,\mathrm{mulVec}\,      \mathrm{eulerPhi}(a_1,a_2,a_3,h,Z),    $
   where the three coefficients are the exact `eulerCoefficients P mu` entries used by the module. Its algebra uses `cross_matrix_adjugate` for arbitrary $Q,u,v$; `adjugate_scaled_inverse` and `adjugate_conjugate` under the hypothesis `IsUnit Q.det`; `cross_inverse_transpose` under `IsUnit Q.det` for arbitrary $u,v$; `nambu_action` for arbitrary $A,B,x,v$; and `liftP_action` for arbitrary $P,X$. The determinant transport needed for the four-dimensional lift is `liftP_unit`, whose hypothesis is `IsUnit P.det`.

3. **Euler-top identity (`euler_top_identity`).** For arbitrary complex $a_1,a_2,a_3,h,\alpha,\beta,\gamma$ satisfying
   $    \alpha^2=a_1,\qquad\beta^2=a_2,\qquad\gamma^2=a_3,    $
   and for every complex $X:\mathrm{Fin}\,4\to\mathbb C$, the lemma proves
   $    T(h,\alpha,\beta,\gamma)\,\mathrm{mulVec}\,      \mathrm{eulerPhi}(a_1,a_2,a_3,h,X)    =-\tfrac18\,g_0\,\mathrm{mulVec}\,      \mathrm{cremona}\bigl(T(h,\alpha,\beta,\gamma)\,\mathrm{mulVec}\,X\bigr),    $
   with the matrix $T$ defined in the module. The separate lemma `det_T`, with no hypotheses, gives
   $    \det T=32\alpha^2\beta^2\gamma^2h^3,    $
   and `g₀_unit`, with no hypotheses, proves `IsUnit g₀.det`.

4. **Assembly (`assembly`).** This lemma takes, as its hypotheses, (i) an Euler identity `he` for all complex $a_1,a_2,a_3,h,\alpha,\beta,\gamma$ and all square-root equalities and all $X$, (ii) the determinant identity `hd` for all $h,\alpha,\beta,\gamma$, (iii) `hg : IsUnit g₀.det`, (iv) a whitening witness `hw` for every real $A,B$ with `A.PosDef`, `B.PosDef`, and the stated rank bound, and (v) a covariance witness `hc` for every real $A,B,h,P,\mu$ under `IsUnit P.det`, $P^{\mathsf T}AP=1$, and $P^{\mathsf T}BP=\operatorname{diagonal}(\mu)$, for every $Z$. For the proposition’s inputs it sets $R=\mathrm{liftP}(P)$, $V=T(h,\alpha,\beta,\gamma)$, and $U=VR^{-1}$, takes $l_1=U$ and $l_2=(-1/8)\,U^{-1}g_0$, and uses the nonzero step size and distinct coefficients to establish both unit-determinant conditions.

## Falsifier

A formal counterexample would have to give real matrices $A,B$ satisfying `A.PosDef`, `B.PosDef`, and $\forall t,\ 2\le\operatorname{rank}(B-t\mathbin{\bullet}A)$, together with $h>0$, for which no complex $l_1,l_2$ with unit determinants satisfy the displayed equality for every complex $X$. A numerical agreement at selected $X$ cannot refute the proposition, because the conclusion is an existential factorisation holding for all $X$. Repeated generalised eigenvalues are outside the proposition and therefore do not falsify this result; they are a neighbouring question requiring a different statement.

## Evidence

The canonical source is `D5/S3/FluidDynamics/Solitons/NambuKahanCremonaDecomposition.lean`.

Frozen state: `Golden/Frozen/state/D5/S3/FluidDynamics/Solitons/NambuKahanCremonaDecomposition.lean.json`.

Declaration statements:
- `result`: `sha256:f0dcc916eb113ef91b7fdebe9043a8397ef4838cce1e27f97a82ffa12602522b`;
- `claim`: `sha256:bbaeddb3e398c682254212d5e54c3ea3e98adc57633e93c72c6771dc7735d1ff`.

The proof of `result` uses only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 conjecture in the concluding remark of a 2024 Ann. Henri Poincaré paper, preregistered in issue #26039 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** For every real $A,B$ satisfying `A.PosDef`, `B.PosDef`, and $\forall t:\mathbb R,\ 2\le\operatorname{rank}(B-t\mathbin{\bullet}A)$, and every real $h$ with $0<h$, there exist complex $4\times4$ matrices $l_1,l_2$ with unit determinants such that the module’s `kahan` lift equals $l_2$ applied by `mulVec` to `cremona` applied to $l_1$ applied by `mulVec` to every complex $X:\mathrm{Fin}\,4\to\mathbb C$.

**Computed, not formalized:** None.

**Argued, not formalized.**

- *Mechanism.* Whitening supplies the diagonal normal form, cross-product covariance transports the Nambu KHK lift to an Euler-top lift, and the explicit $T$ identity then supplies the Cremona factorisation. These ingredients explain the proof mechanism; the public proposition records only the assembled conclusion.
- *Range and sharpness.* The formal range is the simple-pencil rank condition. The source’s assertion that its invariant net has eight distinct base points, and the implication from that geometric condition to the rank hypothesis, are not formalized here, so the relationship between those two genericity descriptions remains open. No claim is made for repeated eigenvalues.
- *Neighbouring statements.* The module does not formalize the source’s type (A) classification, degree-growth conclusions, or any further integrability consequence. Applying those results to the formal range is a separate argument.
- *Effect on the source.* The conjectural decomposition in Remark 7.7 is established on the proposition’s simple-pencil range. The source’s other conjectures and conclusions retain their own hypotheses and are not settled by this declaration.

## ASSUMED-UNVERIFIED

The literature check is bounded to the sources and repository searches recorded in issue #26039; it does not establish exhaustive novelty or priority, and the cited-work readings were not independently reproduced here. The source’s eight-point base-locus assertion, its relation to the rank hypothesis, the converse implication, and all repeated-eigenvalue cases are outside the formal proposition. Statements about projective rational-map consequences, type (A) classification, growth, and integrability beyond the exact homogeneous equality are not formalized. Any source reading or consequence not reproduced in the Lean declarations remains assumed-unverified.
