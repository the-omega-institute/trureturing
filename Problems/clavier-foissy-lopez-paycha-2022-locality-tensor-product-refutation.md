---
slug: clavier-foissy-lopez-paycha-2022-locality-tensor-product-refutation
bibkey: clavieretal2022localitytensor
doi: 10.1007/s40879-025-00822-z
url: https://arxiv.org/abs/2205.14616v1
triage: theorem
motivation_gids:
  - D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.result
---

# Locality tensor products need not be locality vector spaces

## Problem

P. J. Clavier, L. Foissy, D. A. López and S. Paycha, *Tensor products and the Milnor-Moore theorem in the locality setup*, arXiv:2205.14616v1 (European Journal of Mathematics 11, 41, 2025), Conjectural statement 6.16, states:

> Given a locality vector space $( {E},\top)$ and $V_1$, $V_2$ two of its subspaces, the subspace $I_{\rm bil} {(V_1, V_2)} {\cap\mathbb{K}(V_1\times_\top V_2)}\subset \mathbb{K}(V_1\times_\top V_2)$ is locality compatible with $\top_{V_1\times_\top V_2}$.

The locator is the downloaded TeX `Clavier_Foissy_Lopez_Paycha_arxiv.tex`, lines 1984–1987, label `conj:main1`, md5 `1f6041a82cd80114573aa776694ccf20`. Quotations expand typesetting macros without changing the wording.

The paper's Notations, `Clavier_Foissy_Lopez_Paycha_arxiv.tex`, line 321, specifies that $\mathbb K$ is a commutative field of characteristic zero. Both conjectures below, under both generator-relation readings, quantify over fields of characteristic zero. The thesis states no characteristic restriction; refuting its assertion even on characteristic-zero fields also refutes the unrestricted assertion.

The tensor-product conjecture is stated explicitly by P. J. Clavier, *TRAPs, Generalisations of MZVs, Locality and Resurgence for Quantum Field Theories*, arXiv:2506.09493v1 (2025), chapter `LOC.tex`, lines 1797–1799, label `conj:loc_tensor`, md5 `41f5e772e40d5eaf8583e8903293dbbb`:

> Let $(E,\top)$ be any locality vector space, $V$ and $W$ any two locality vector subspaces of $E$. Then $(V\otimes_\top W,\overline{\top})$ is a locality vector space.

For a field $\mathbb K$, a locality vector space is a $\mathbb K$-vector space $E$ with a symmetric relation $r$, with $r(0,0)$, such that the polar $U^r=\{x:\forall u\in U,\ r(u,x)\}$ of every subset $U\subseteq E$ is a linear subspace. For subspaces $V,W\subseteq E$, put $F=\mathbb K(V\times_\top W)$, the free span of pairs $(v,w)\in V\times W$ satisfying $r(v,w)$. In the ambient free span on all pairs, let $I_{\rm bil}(V,W)$ be the span of the two additivity and two scalar-multiplication relations, and put $I=F\cap I_{\rm bil}(V,W)$.

The module uses two generator relations on pairs $(v,w)$ and $(v',w')$:

- `Prod.RProd r r`: $r(v,v')\wedge r(w,w')$, as in the 2022 paper, Eq. `eq:locreltoptimes`, TeX lines 447–449;
- `fourWay`: $r(v,w)\wedge r(v,v')\wedge r(v,w')\wedge r(w,v')\wedge r(w,w')\wedge r(v',w')$, all six pairs among the four entries, as in the thesis's locality cartesian power, Eq. `eq:lprod`, `LOC.tex` lines 219–221, and its description of tensor locality through $E^{\times_\top4}$, lines 743–747.

The sources disagree: the paper's Remark at lines 1972–1975 identifies its componentwise relation, when $V=W$, with $V^{\times_\top4}$, whereas the thesis's cartesian-power definition requires all six pairs to be related. The two generator relations differ in general, even on local pairs; the computed example in Triage distinguishes them.

For either generator relation $g$, write $s_g(a,b)$ when every pair in the support of $a\in F$ is $g$-related to every pair in the support of $b\in F$. The relation on $F/I=V\otimes_\top W$ is existential: two classes are related precisely when they have $s_g$-related representatives. Locality compatibility of $I$ means that for all $x,y,z\in F$ and $w\in I$, if $s_g(x,y)$ and $s_g(x+w,z)$, there is $w'\in I$ with both $s_g(x+w',y)$ and $s_g(x+w',z)$.

The problem is tracked in issue [#21552](https://github.com/the-omega-institute/trureturing/issues/21552), including [comment 6396883196](https://github.com/the-omega-institute/trureturing/issues/21552#issuecomment-6396883196). The module defines `TensorConjecture g` as the tensor-product assertion and `PairConjecture g` as the compatibility assertion for the chosen generator relation, each universally quantified over every field $\mathbb K$ of characteristic zero, every $\mathbb K$-vector space $E$ in `Type`, every locality relation and every pair of subspaces, without a finite-dimensionality hypothesis. The module defines `claim := TensorConjecture (fun _ r => Prod.RProd r r) ∨ TensorConjecture fourWay ∨ PairConjecture (fun _ r => Prod.RProd r r) ∨ PairConjecture fourWay` and proves `result : ¬ claim`, refuting both universal assertions for each generator relation.

The definitions and source locators are recorded in [the paper note](../Library/HomologicalAlgebra/clavieretal2022localitytensor.md) and [the thesis note](../Library/HomologicalAlgebra/clavier2025localityhdr.md).

## Motivation

Locality tensor products are used to build tensor algebras, enveloping algebras and the locality version of the Milnor–Moore theorem. The source distinguishes constructions in the pre-locality setting from stronger constructions requiring every polar to be a subspace. The conjectures would supply the compatibility needed to pass to that stronger setting for arbitrary locality vector spaces. Their refutation identifies a restriction that such constructions must retain or replace.

## Gap

The bounded literature check preregistered in #21552 reports:

- the 2022 arXiv source retains Conjectural statement 6.16, and the 2025 thesis retains the tensor-product conjecture;
- the journal abstract, citation listings, arXiv author searches and Zenodo searches supplied no settlement in the searched scope;
- the repository search supplied no existing settlement.

The two quoted arXiv source statements are directly checked at the locators above. The other search readings are attributed to the preregistration's authors under ASSUMED-UNVERIFIED. The literature status is `not-found-in-searched-scope`.

## Route

All witness coordinates are indexed by $0,1,2,3,4$, matching `Fin 5` in Lean. Take $\mathbb K=\mathbb R$, $E=\mathbb R^5$ and $V=W=E$. Let $P(v)=(v_0,v_1,v_2)$ and let $\ell_0,\ldots,\ell_5$ be the lines in $\mathbb R^3$ spanned, in order, by $(0,1,0)$, $(1,1,0)$, $(1,-1,0)$, $(0,0,1)$, $(1,0,1)$ and $(1,0,-1)$. Define $R(v,t)$ by the conjunction of $P(v)=0$ or $P(t)=0$ or membership of both projections in a common $\ell_i$, and the four equations $v_3t_2=t_3v_2=v_4t_1=t_4v_1=0$.

For either generator relation $g$, write $s=s_g$ and $\overline R$ for its existential quotient relation; $s_{\rm comp}$ denotes the componentwise support relation.

1. **A locality relation.** `line_unique` says that for a nonzero $u\in\mathbb R^3$ and $i,j\in\mathrm{Fin}\,6$, membership $u\in\ell_i$ and $u\in\ell_j$ forces $i=j$. Thus `mem_projectedPolar` identifies the projected singleton polar at any $v\in E$ as all of $E$ if $P(v)=0$, the inverse image of the unique line containing $P(v)$ if $P(v)\ne0$ lies on a listed line, and $\ker P$ otherwise. `mem_singletonPolar` intersects this subspace with the four linear kernels defining the additional equations. `rel_locality` establishes symmetry, $R(0,0)$ and the subspace property for every polar, using arbitrary intersections of singleton polar submodules.
2. **Local representatives.** Write $[v,t]$ for a generator of the ambient free span and $e_i$ for a coordinate vector. Define $X_k=\tfrac12[e_0+e_k,e_0+e_k]+\tfrac12[e_0-e_k,e_0-e_k]-[e_k,e_k]$ and $Y_i=[e_i,e_i]$. `X_supported` places $X_k$ in $F$ under the hypothesis $k=1$ or $k=2$; `Y_supported` places $Y_i$ in $F$ under $i=3$ or $i=4$. For every $k\in\mathrm{Fin}\,5$, `X_polarization` gives $X_k-Y_0\in I_{\rm bil}(E,E)$ in the ambient free span. `X_difference` gives $X_2-X_1\in I_{\rm bil}(E,E)$; its local support therefore puts it in $I$. `X_related` gives $s(X_k,Y_i)$ under the hypothesis $(k=1\ \text{and}\ i=3)$ or $(k=2\ \text{and}\ i=4)$, for any generator relation that relates $(v,v)$ to $(w,w)$ whenever $R(v,v)$, $R(w,w)$ and $R(v,w)$. The witnesses have only diagonal generators $(v,v)$ with $R(v,v)$; both `Prod.RProd r r` and `fourWay` satisfy the required implication.
3. **Functionals.** For every $i\in\mathrm{Fin}\,5$, let $\phi_i$ be the linear extension of $[v,t]\mapsto v_it_i$. `phi_vanishes` gives $\phi_i(a)=0$ for every ambient free-span element $a\in I_{\rm bil}(E,E)$. `phi_support` says that whenever $\phi_i(a)\ne0$, some support pair $(v,t)$ of that ambient element has $v_it_i\ne0$. `phi_values` gives $\phi_0(X_1)=1$ and $\phi_3(Y_3+Y_4)=\phi_4(Y_3+Y_4)=1$. The direct evaluations in `pair_refuted` also give $\phi_3(Y_3)=\phi_4(Y_4)=1$. `phi_quotient` gives $\phi_i(a)=\phi_i(b)$ whenever $a,b\in F$ have the same class in $F/I$.
4. **Simultaneous obstruction.** `key_obstruction` assumes $v,t\in E$, $R(v,t)$ and $v_0t_0\ne0$, and concludes $v_1\ne0$ or $v_2\ne0$. `no_joint_related` assumes $a,b,c\in F$, $\phi_0(a)\ne0$, $\phi_3(b)\ne0$, $\phi_4(c)\ne0$, $s_{\rm comp}(a,b)$ and $s_{\rm comp}(a,c)$, and concludes a contradiction. Indeed, support pairs selected by `phi_support` force a first component $v$ of a support pair of $a$ to satisfy both $v_2=0$ and $v_1=0$, contradicting `key_obstruction` for that local pair. Four-way relatedness implies componentwise relatedness, so the same obstruction excludes four-way support comparisons.
5. **Compatibility is refuted.** `pair_refuted` uses $x=X_1$, $y=Y_3$, $z=Y_4$ and $w=X_2-X_1\in I$. The two premises are $s(X_1,Y_3)$ and $s(X_1+w,Y_4)=s(X_2,Y_4)$. Any compatibility adjustment $w'\in I$ would make $a=X_1+w'$ related to both $b=Y_3$ and $c=Y_4$, with $\phi_0(a)=\phi_3(b)=\phi_4(c)=1$, contradicting `no_joint_related` after reducing the support comparisons to componentwise ones.
6. **The quotient polar is not additive.** In `tensor_refuted`, let $q:F\to F/I$ be the quotient map. The witnesses give $q(X_2)=q(X_1)$, $q(X_1)\mathrel{\overline R}q(Y_3)$ and $q(X_1)\mathrel{\overline R}q(Y_4)$. If the singleton polar of $q(X_1)$ were a subspace, it would also contain $q(Y_3+Y_4)$. Related representatives $a,b\in F$ of $q(X_1)$ and $q(Y_3+Y_4)$ would satisfy $\phi_0(a)=\phi_3(b)=\phi_4(b)=1$ by `phi_quotient`. Applying `no_joint_related` to $a,b,b$, with the same componentwise support relation in both hypotheses, is impossible. `result` instantiates the parameterized `tensor_refuted` and `pair_refuted` at both `Prod.RProd r r` and `fourWay` to negate the four-part disjunction.

## Falsifier

The refutation would not settle the source statements if it used a different denominator or a different quotient relation. The module encodes:

- `bilRelations` as the ambient span of all four bilinearity families with their entries in $V,W$, including generators that need not themselves have local support;
- `freeSpan` as the submodule supported on the local pairs, and `bilIdeal` as its intersection with the ambient bilinearity submodule;
- `localityTensor` as the quotient of that free-span submodule by the inverse image of the intersection under its inclusion;
- `spanRel` as all cross-support comparisons with the chosen generator relation, `Prod.RProd r r` or `fourWay`, and `quotientRel` as existence of related representatives, including the usual vacuous conditions for an empty support;
- `IsLocalityVectorSpace` as symmetry, related zeros and the subspace property for every polar, and `LocalityCompatible` with all three test elements and both adjustments quantified as in the source.

The componentwise reading matches the paper's TeX lines 340–359, 387–394, 422–430, 447–449, 556–564, 755–769 and 1880–1886. The four-way reading uses the thesis's cartesian power in `LOC.tex`, lines 219–221, and tensor locality at lines 743–747. Both use the existential quotient relation in `LOC.tex`, lines 606–612. In particular, $X_k-Y_0$ is used only in the ambient bilinearity submodule: the proof does not assume that $[e_0,e_0]$ is a local generator.

## Evidence

The canonical source is `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.lean` (488 lines), with both conjectures quantified over characteristic-zero fields.

- **Proof.** It proves `result : ¬ claim`, where `claim := TensorConjecture (fun _ r => Prod.RProd r r) ∨ TensorConjecture fourWay ∨ PairConjecture (fun _ r => Prod.RProd r r) ∨ PairConjecture fourWay`. Both refutations use the same self-related diagonal generators for their positive comparisons, and four-way relatedness reduces to componentwise relatedness for the obstruction.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.lean.json`, statement `sha256:a3a283bff452be76702cc7a6bf75a334e3305461ac2f81db9a98179a01f5cafc`.

Declaration statements:

- `result`: `sha256:499d4a8e8eec2070dc1c31af1890839a779f151817f50da5021aacf343ccce25`;
- `claim`: `sha256:2949345f6ba19ae99ba62b93f7d9f6799036d583955387d6890b4e8ae1c9b14e`.

## Triage

Tier 1 by settlement size, an explicit counterexample to the conjectures of the 2022 preprint and the 2025 thesis, preregistered in issue #21552 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the disjunction `TensorConjecture (fun _ r => Prod.RProd r r) ∨ TensorConjecture fourWay ∨ PairConjecture (fun _ r => Prod.RProd r r) ∨ PairConjecture fourWay` is false. Thus neither the tensor-product assertion nor the compatibility assertion, quantified over all fields $\mathbb K$ of characteristic zero, all $\mathbb K$-vector spaces $E$ in `Type`, all locality relations and all pairs of subspaces, as stated in Problem, is valid for either generator relation.

**Computed, not formalized** (exact rational arithmetic, `c11281b496c6d78e4f59f67f-witness-check.py`; every item reproduced by the orchestrator by hand): the eight displayed diagonal generator pairs for $X_1,X_2,Y_3,Y_4$ are local. Each of the three support comparisons for $s(X_1,Y_3)$ and for $s(X_2,Y_4)$ returns true; each of the three comparisons for $s(X_1,Y_4)$ and for $s(X_2,Y_3)$ returns false. Both displayed $X_k$, for $k=1,2$, have ordinary tensor image $e_0\otimes e_0$, checked in all 25 matrix entries. These computations concern only the displayed elements and do not search over alternative representatives.

**Computed, not formalized** (exact rational arithmetic, `897e6c2b7777b5096b06f995-witness-check.py`; every item reproduced by the orchestrator by hand): each of the three four-way support comparisons for $s_{\rm fourWay}(X_1,Y_3)$ and for $s_{\rm fourWay}(X_2,Y_4)$ returns true; each of the three for $s_{\rm fourWay}(X_1,Y_4)$ and for $s_{\rm fourWay}(X_2,Y_3)$ returns false. The local generator pairs $(e_0,e_3)$ and $(e_3,e_0)$ are componentwise related but not four-way related, since $R(e_0,e_0)$ is false.

**Argued, not formalized.**

- *Mechanism and missing structure.* Existential quotient relatedness permits a different representative for each test. Additivity of a quotient polar requires the tests to be jointly satisfiable. The compatibility condition is a sufficient simultaneous-adjustment property; the formal obstruction in Route specifies its failure for elements $a,b,c\in F$ satisfying $\phi_0(a)\ne0$, $\phi_3(b)\ne0$, $\phi_4(c)\ne0$, $s_{\rm comp}(a,b)$ and $s_{\rm comp}(a,c)$ (`no_joint_related`). Four-way relatedness supplies these componentwise hypotheses, and the self-related diagonal witnesses supply the positive comparisons for both generator relations. The construction uses a finite-dimensional space and $V=W=E$, so neither finite dimensionality nor equality of the two subspaces suffices to repair either reading of the conjectures.
- *A surviving conditional statement.* For any locality $\mathbb K$-vector space $(F,s)$ and any locality-compatible subspace $I$, the existential quotient relation has subspace polars. To check this directly, fix a class $[u]$ and two classes $[a],[b]$ in its polar. Choose witnesses $s(u_1,a_1)$ and $s(u_2,b_1)$ with $u_1,u_2\in[u]$, $a_1\in[a]$ and $b_1\in[b]$. Since $u_2-u_1\in I$, compatibility supplies $u_*\in[u]$ related to both $a_1$ and $b_1$. The polar of $u_*$ is a subspace, so $u_*$ is related to $\alpha a_1+\beta b_1$ for all $\alpha,\beta\in\mathbb K$. This gives closure of the quotient singleton polar under linear combinations; it contains zero, and all other polars are intersections of singleton polars. Symmetry and related zeros descend as well. This is the conditional quotient theorem labelled `thm:quotientlocality-vs` in Clavier–Foissy–López–Paycha (2022), arXiv:2205.14616v1, TeX lines 1935–1940. Its extra compatibility hypothesis is retained.
- *A surviving special case.* If the relation on $E$ is total, every pair in $V\times W$ is local and every two elements of $F$ are support-related. Every two quotient classes therefore have related representatives, so their relation is total and every polar is the entire quotient. This verifies the tensor-product assertion for both generator relations under that additional hypothesis. Minimal counterexample dimension and a general classification of relations that preserve tensor locality are open here.
- *Effect on the paper.* The corollary labelled `cor:ntensorproduct` in Clavier–Foissy–López–Paycha (2022), arXiv:2205.14616v1, TeX lines 2005–2009, assumes `conj:main1` and concludes that for every $n\ge1$ and any $n$ linear subspaces of a locality vector space their locality tensor product is a locality vector space. Its unconditional version is false already for $n=2$, for either the componentwise or the four-way generator relation. The enhanced universal property `thm:univpropltp` (lines 2082–2096) likewise assumes `conj:main1` for the given $V,W$; one cannot use that conjecture to place every such tensor product in the category of locality vector spaces. The pre-locality constructions and conditional conclusions with separately verified compatibility hypotheses are not contradicted. The locality Cartier–Quillen–Milnor–Moore theorem `thm:CQMMTheorem` (lines 2538–2544) retains the distinct assumptions `conj:main2` and `conj:univenvalg` on the primitive locality Lie algebra of a graded, connected, cocommutative locality Hopf algebra. Those filtered tensor-algebra and enveloping-ideal conditions are not formalized or independently settled here; this module supplies no counterexample to an individual Hopf algebra satisfying them.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. Issue #21552 attributes the journal abstract, arXiv version and Paycha/Foissy author searches, Zenodo searches and repository search to the orchestrator. It records OpenAlex counts of one citing work for W4281726070 and zero for W4411344671, and zero Zenodo records for “locality tensor product” and “locality vector space”. The identification of that citing work as Dahmen–Paycha–Schmeding, arXiv:2206.13993, and its failure to settle the problem are search-seat reports carried by the issue. These search readings and the citing work were not independently reproduced. The subscription journal text was not read; the source statements checked here are the specified arXiv versions.

The 2022 e-print is a single gzip file whose header names `Clavier_Foissy_Lopez_Paycha_arxiv.tex`; issue #21552 calls the same file (same md5) `main.tex`. Clavier's 2025 thesis, `LOC.tex` line 1802, attributes a locality-basis special case to the paper's Theorem 6.4 and refers to its Definition 6.1. Those particular locators were not reproduced in the checked 2022 arXiv text, so no locality-basis theorem or assertion that this witness has no locality basis is claimed here.

The computations and the arguments labelled “Computed, not formalized” and “Argued, not formalized”, including their conclusions about surviving restrictions and consequences for other source statements, are not additional Lean theorems. Neither a minimal dimension nor a classification of repairs is established. The precise filtered tensor-algebra and enveloping-algebra conjectures, their implications and their validity on particular Lie or Hopf algebras are not checked by `result`.
