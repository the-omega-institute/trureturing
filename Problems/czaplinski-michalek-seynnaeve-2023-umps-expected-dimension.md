---
slug: czaplinski-michalek-seynnaeve-2023-umps-expected-dimension
bibkey: czaplinskimichalekseynnaeve2023umps
doi: 10.1016/j.aam.2022.102417
url: https://arxiv.org/abs/1904.07563v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation.result
---

# Two-site uniform matrix product states need not have expected dimension

## Problem

A. Czapliński, M. Michałek and T. Seynnaeve, *Uniform matrix product states from an algebraic geometer's point of view*, arXiv:1904.07563v1 (2019; Adv. Appl. Math. 142 (2023), 102417), Section 2, Conjecture 2.14:

> For every choice of $(D,d,N)$, $\IMPS(D,d,N)$ has expected dimension.

This is the verbatim text of `uMPS-final.tex`, line 312, inside the conjecture at lines 311–313; the source's macro `\IMPS` denotes uMPS. Definition 2.1 fixes $D,d,N\ge1$. For $d$ complex $D\times D$ matrices, the coefficient indexed by a word $(i_1,\ldots,i_N)$ is $\operatorname{tr}(M_{i_1}\cdots M_{i_N})$, and $\mathrm{uMPS}(D,d,N)$ is the image of this parametrization (lines 180–193).

The expected-dimension equality in lines 299–305 is

$\dim\overline{\mathrm{uMPS}(D,d,N)}=\min\{(d-1)D^2+1,\dim\mathrm{Cyc}^N(\mathbb C^d)\}$,

where $\mathrm{Cyc}^N(\mathbb C^d)$ is the space of cyclically invariant tensors (line 209). Dimension is interpreted through the coordinate ring of the Zariski closure, as in the preregistration and the module's `varietyDim`. The source introduces this closure at line 211 and its dimension bound at lines 272–274.

Issue [#23659](https://github.com/the-omega-institute/trureturing/issues/23659) fixes this universal reading. It is refuted at $(D,d,N)=(2,5,2)$. The definitions and source locators are also recorded in [the literature note](../Library/Geometry/czaplinskimichalekseynnaeve2023umps.md).

## Motivation

Uniform matrix product states represent tensors by repeating one matrix tuple at every site. Their dimension measures the number of independent complex parameters visible in the resulting tensors. The conjecture asserts that the parameter count after allowing for simultaneous conjugation and the cyclic ambient dimension are the only dimension restrictions. A two-site rank constraint tests that assertion directly.

## Gap

The bounded literature check recorded in issue #23659 reports:

- no exception identified in Bernardi–De Lazzari–Gesmundo (2021), arXiv:2101.03148, the three additional arXiv sources and the AGATES open-problem collection identified there;
- no settlement or correction identified in the available citing texts from the reported seven OpenAlex works and nine Semantic Scholar entries;
- no earlier repository result for this source in the recorded issue and content searches.

`not-found-in-searched-scope`. These reports do not establish exhaustive novelty or priority.

## Route

All the dimension comparisons below concern the fixed positive triple $(b,d,n)=(2,5,2)$, with the module's $b$ equal to the source's $D$. Let $U=\{(i,j)\in\mathrm{Fin}\,5\times\mathrm{Fin}\,5:i\le j\}$, let $P=\mathbb C[y_p:p\in U]$, and let $A$ be the coordinate ring used in `varietyDim (uMPS 2 5 2)`.

1. **Cyclic dimension.** `cyclic_finrank_lower` states that the complex dimension of the fixed submodule for two-site rotation on five symbols is at least $15$. Its injective linear map sends $v:U\to\mathbb C$ to the coefficient function $i\mapsto v(\min(i(0),i(1)),\max(i(0),i(1)))$. Evaluation on the ordered pairs recovers $v$; `card_UT` gives $|U|=15$.
2. **A singular trace Gram matrix.** For every $m:\mathrm{Fin}\,5\to\operatorname{Mat}_{2\times2}(\mathbb C)$ and every word $i:\mathrm{Fin}\,2\to\mathrm{Fin}\,5$, `traceWord_two` identifies its coefficient with $\operatorname{tr}(m_{i(0)}m_{i(1)})$. For every such $m$, `gram_factorization` writes $S_{ij}=\operatorname{tr}(m_i m_j)$ as $XY$, with $X_{i,(a,c)}=(m_i)_{ac}$ and $Y_{(a,c),j}=(m_j)_{ca}$ for $(a,c)\in\mathrm{Fin}\,2\times\mathrm{Fin}\,2$. The map represented by $Y$ has a five-dimensional domain and four-dimensional codomain. Its nonzero kernel vector also lies in the kernel of $S$. Thus `gram_det_zero` gives $\det S=0$ for every such matrix tuple, with no invertibility or nonzero-matrix hypothesis.
3. **The symmetric coordinate ring.** For all $i,j\in\mathrm{Fin}\,5$, `coordinate_symmetry` puts $x_{ij}-x_{ji}$ in the vanishing ideal, using commutation of the trace of a product. `coordinateMap` sends $y_{(i,j)}$ to the class of $x_{ij}$ for $(i,j)\in U$. For every $i,j\in\mathrm{Fin}\,5$, `coordinateMap_variable` identifies the image of the variable at their sorted pair with the class of $x_{ij}$. Consequently `coordinateMap_surjective` gives a surjective complex algebra map $\psi:P\to A$.
4. **A genuine dimension drop.** `symmetricDet` is $\Delta=\det(y_{\min(i,j),\max(i,j)})$. Evaluating its diagonal variables at $1$ and its other variables at $0$ yields $1$, so `symmetricDet_ne_zero` gives $\Delta\ne0$. The polynomial ring $P$ is a domain, hence $\Delta$ is a nonzero divisor; `coordinateMap_det_zero` gives $\psi(\Delta)=0$. For this surjective ring homomorphism between commutative rings, with this nonzero divisor in its kernel, Mathlib's `ringKrullDim_succ_le_of_surjective` gives $\dim A+1\le\dim P$. The finite set $U$ has $15$ elements and $\mathbb C$ is a Noetherian field of Krull dimension zero, so `MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite` gives $\dim P=15$. `actual_dimension_upper` concludes `varietyDim (uMPS 2 5 2)` $\le14$ in $\mathrm{WithBot}\,\mathbb N_\infty$.
5. **Contradiction.** The positive triple satisfies every hypothesis of `claim`. At this triple its first bound is $17$, and `cyclic_finrank_lower` makes its second bound at least $15$. Thus the asserted minimum is at least $15$. Substituting the asserted equality contradicts `actual_dimension_upper`; `result` concludes $\neg\texttt{claim}$.

## Falsifier

The refutation would miss the source conjecture if its tensors, dimension or quantifiers differed from the source's. Here:

- `traceWord` multiplies the same family of arbitrary complex matrices in site order and takes the ordinary trace; `uMPS` is its full image, with no normalization, Hermitian or projective restriction.
- `claim` quantifies over all natural $b,d,n$ with $0<b$, $0<d$ and $0<n$. Its cyclic space is the fixed submodule of precomposition by `finRotate n`, and its minimum is taken in $\mathbb N$ and cast to $\mathrm{WithBot}\,\mathbb N_\infty$.
- `varietyDim` is the Krull dimension of $\mathbb C[x_i:i\in\mathrm{Fin}\,n\to\mathrm{Fin}\,d]/I(\mathrm{uMPS})$. It measures the Zariski closure, rather than the linear span or the dimension of the parameter domain.
- The determinant is nonzero in the polynomial ring on the $15$ independent symmetric coordinates. Its vanishing therefore imposes a restriction beyond cyclic symmetry.

The proof requires only an upper bound of $14$ on the actual dimension and a lower bound of $15$ on the conjectured minimum. It does not require an exact dimension computation.

## Evidence

The canonical source is `D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** `#print axioms` reports only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:2c22c82e42e6019ec0646e8419b32c14cf6f3de3bf6998b2f7f5c06e5cb01ce9`;
- `claim`: `sha256:e06ee6fcafc782a5bf0154f97e18fa93fa745387542e8aca668695772d1451af`.

## Triage

Tier 1 conjecture of a 2019 preprint with a 2023 journal publication, preregistered in issue #23659 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that, for every positive bond dimension, physical dimension and number of sites, the coordinate-ring dimension of the trace-word image equals the minimum of $(d-1)D^2+1$ and the complex dimension of the cyclic fixed submodule.

**Computed, not formalized** (orchestrator, recorded in #23659): the source's cyclic-dimension formula and parameter bound give the expected value at $(2,5,2)$, and a rank count of symmetric matrices gives the dimension of the two-site image.

**Argued, not formalized.**

- *Mechanism.* For the five complex $2\times2$ matrices in `gram_factorization`, the two-site coefficients retain their bilinear trace Gram matrix; `gram_det_zero` captures the restriction from its four-dimensional intermediate space. This permits a nonlinear relation even when the conjugacy parameter count exceeds the cyclic ambient dimension. Counting conjugacy redundancy and cyclic coordinates alone does not ensure that the image fills that space.
- *A two-site repair and sharpness.* The source's description at lines 250–252 is “all symmetric $d \times d$-matrices of rank at most $D^2$”. It has the following ordinary algebraic explanation. For positive $D,d$, put $q=D^2$. The symmetric bilinear trace pairing on $\operatorname{Mat}_{D\times D}(\mathbb C)$ is nondegenerate: each matrix unit pairs with its transpose. A basis change identifies it with the standard nondegenerate symmetric form on $\mathbb C^q$. Every complex symmetric matrix of rank at most $q$ is congruent to a diagonal matrix with that many nonzero diagonal entries; taking their square roots realizes it as a Gram matrix in $\mathbb C^q$. Thus the two-site image has exactly the source's rank description. For rank $k$, choose an invertible principal $k\times k$ block $B$. In that chart a symmetric matrix has block form $\left(\begin{smallmatrix}B&C\\C^{\mathsf T}&C^{\mathsf T}B^{-1}C\end{smallmatrix}\right)$, leaving $k(k+1)/2+k(d-k)$ parameters. These charts cover the rank-$k$ stratum; including rank zero and maximizing over $k\le r=\min\{d,q\}$ gives $rd-r(r-1)/2$. At $(2,5,2)$ this is $14$. This dimension argument and its equality conclusion are not formalized by `result`.
- *Nearby cases.* The same unformalized formula gives the expected dimension at $N=2$ when $d\le D^2$, and also when $D=1$. For $N=2$, $D\ge2$ and $d>D^2$, put $q=D^2$; the parameter bound exceeds the rank-variety dimension by $q(q-3)/2+1$, and the symmetric ambient dimension exceeds it by $(d-q)(d-q+1)/2$. Both are positive, giving an unformalized family of further defects. Restricting the conjecture to $N\ge3$ excludes this two-site obstruction; the unrestricted equality in that range remains open here.
- *Effect on the source.* Conjecture 2.14 cannot justify a universal expected-dimension equality or an unrestricted inference of ambient filling from the two numerical bounds. Its only explicit reference outside the conjecture in the source TeX is line 314, which derives special cases from separately proved results. In particular, the ambient-filling corollary at lines 569–574 assumes $D\ge N\dim\mathrm{Cyc}^N(\mathbb C^d)$, and the generic-identifiability corollary at lines 706–735 assumes $N\ge2GC_{D,d}+1$. Their proofs do not invoke Conjecture 2.14, so refuting it does not invalidate those arguments. The table concerns $d=2$; the counterexample at $d=5$ does not contradict its reported cases.

## ASSUMED-UNVERIFIED

The bounded literature check establishes no exhaustive worldwide novelty or priority. The full-text and citation screenings recorded in #23659 for Bernardi–De Lazzari–Gesmundo, arXiv:2101.03148; arXiv:2304.10570, arXiv:2212.14095 and arXiv:1911.10411; the AGATES collection; and the seven OpenAlex and nine Semantic Scholar entries remain unreproduced here. The journal version's retention of Conjecture 2.14 is reported in #23659 and remains unverified against the journal text. The repository search results are those recorded in the preregistration, without an independent exhaustive search.

The computations and every argument in the corresponding labelled groups are outside the formal statement of `result`. In particular, exact dimension $14$, the general two-site dimension formula and its classification of further defects and surviving cases are not formalized here. The assessment of the source's proof dependencies is a reading of its TeX, without Lean formalization of those results. Expected dimension for every positive $D,d$ and $N\ge3$ is not settled by this refutation.
