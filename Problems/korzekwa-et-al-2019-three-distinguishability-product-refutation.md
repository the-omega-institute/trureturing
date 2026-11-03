---
slug: korzekwa-et-al-2019-three-distinguishability-product-refutation
bibkey: korzekwaetal2019distinguishing
doi: 10.1088/1751-8121/ab30f7
url: https://arxiv.org/abs/1812.09083v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurements/ThreeDistinguishabilityProductRefutation.result
---

# The three-distinguishability region in dimension four is not of product form

## Problem

K. Korzekwa, S. Czachórski, Z. Puchała and K. Życzkowski, *Distinguishing classically indistinguishable states and channels*, J. Phys. A: Math. Theor. 52, 475303 (2019), arXiv:1812.09083v3, conjecture in Section III.B, Eq. (30), `Distinguishability.tex` lines 462–467 (notation macros expanded):

> Moreover, based on numerical evidence, we conjecture that points belonging to $\mathcal A^3_4$ have the following product structure:
>
> $a b \boldsymbol{f}^1+a (1-b) \boldsymbol{f}^2+(1-a) b \boldsymbol{f}^3+(1-a) (1-b) \boldsymbol{f}^4,$
>
> with $a,b\in[0,1]$.

The source defines $\mathcal A_d^M$ by the existence of $M$ perfectly distinguishable quantum states with the same classical version (`Distinguishability.tex`, lines 147–149), defines that version as the diagonal in the preferred basis (lines 236–241), and identifies perfect distinguishability with pairwise orthogonal supports (lines 297–300). The $\boldsymbol f^i$ are the four face centres of the probability simplex, each a permutation of $(1,1,1,0)/3$ (line 462). The definitions and quotation are also recorded in [the literature note](../Library/HilbertOperators/korzekwaetal2019distinguishing.md).

For the formal statement, index the four coordinates and face centres by $0,1,2,3$, and put $f^j_k=(1-\delta_{jk})/3$. `InRegion p` means that $p$ is nonnegative with coordinate sum one and that there exist three complex $4\times4$ positive semidefinite matrices $\rho_i$ of trace one satisfying $\rho_i\rho_j=0$ for $i\ne j$ and $\operatorname{Re}(\rho_i)_{kk}=p_k$ for every $i,k$. `ProductForm f p` is precisely the displayed combination with $a,b\in[0,1]$.

Issue [#25867](https://github.com/the-omega-institute/trureturing/issues/25867) fixes `claim`: there exists a permutation $\sigma$ of the four face centres such that every $p$ satisfying `InRegion p` has `ProductForm` with centres $f^{\sigma(0)},\ldots,f^{\sigma(3)}$. The existential labelling accommodates the different conventions in the source's text and figure. The module proves `result : ¬ claim`.

## Motivation

The source relates $M$-distinguishability to storing $\log_2 M$ bits in coherence while keeping the classical diagonal fixed (Section I, lines 151–165). A characterization of $\mathcal A^3_4$ would therefore decide exactly which four-outcome classical distributions admit three perfectly distinguishable coherifications. The conjecture proposes a two-parameter description of this smallest case between the source's separately treated regimes $M=2$ and $M=d$.

## Gap

The bounded literature check recorded in #25867 before any Lean reports:

- the conjecture remains in arXiv:1812.09083v3;
- INSPIRE listed seven citing works, arXiv:1903.12448, 1911.07677, 2310.13045, 2104.06062, 1911.12373, 2011.02994 and 2103.08208; the preregistration reports no treatment of $\mathcal A^3_4$ or Eq. (30) in them;
- repository searches for the source identifier and distinguishability preregistrations found no prior record in issues, `Problems/` or `Library/`.

`not-found-in-searched-scope`. The source conjecture was checked directly in the v3 TeX; the citation search and the reported readings of the seven citing works were not independently reproduced.

## Route

All lemma names below refer to the private helpers of the canonical module, and all coordinates in the construction refer to its fixed `point`.

1. **The common diagonal.** Put $r=\sqrt5$, $\alpha=(5-r)/10$, $\beta=(5-r)/20$, $\gamma=(r-1)/4$ and $p=(\alpha,\beta,\alpha,\gamma)$. The hypothesis-free lemma `point_simplex` establishes $p_k\ge0$ for every $k\in\mathrm{Fin}\,4$ and $\sum_kp_k=1$.
2. **The orthogonal triple.** For the fixed $\zeta=\exp(i\pi/5)$, the three `state` vectors are $(\sqrt\alpha,\sqrt\beta,\sqrt\alpha,\sqrt\gamma)$, $(\sqrt\alpha,\sqrt\beta\zeta^2,\sqrt\alpha\zeta^4,\sqrt\gamma\zeta^7)$ and $(-\sqrt\alpha,\sqrt\beta\zeta^9,\sqrt\alpha\zeta^3,\sqrt\gamma\zeta^9)$. The hypothesis-free lemmas `phase_unit`, `phase_fifth` and `phase_quadratic` establish $\overline\zeta\zeta=1$, $\zeta^5=-1$ and $\zeta^2=((1+\sqrt5)/2)\zeta-1$ for this $\zeta$. For $i,j\in\mathrm{Fin}\,3$ with $i\ne j$, `weighted_orthogonality` proves $\sum_k p_k\overline{\mathrm{phases}_{ik}}\mathrm{phases}_{jk}=0$, and `state_orthogonality` proves $\langle\mathrm{state}_i,\mathrm{state}_j\rangle=0$. For every $i\in\mathrm{Fin}\,3$ and $k\in\mathrm{Fin}\,4$, `state_diagonal` proves $\mathrm{state}_{ik}\overline{\mathrm{state}_{ik}}=p_k$, with the real value embedded in $\mathbb C$. The hypothesis-free lemma `density_region` constructs $\rho_i=|\mathrm{state}_i\rangle\langle\mathrm{state}_i|$ and establishes `InRegion point`, including positivity, trace one, zero products for distinct indices and the common diagonal.
3. **The obstruction for every labelling.** For any permutation $\sigma$ of $\mathrm{Fin}\,4$ and any real vector $p$, under the hypothesis `ProductForm` with the relabelled face centres, `product_pairing` proves $q_{\sigma(0)}q_{\sigma(3)}=q_{\sigma(1)}q_{\sigma(2)}$, where $q_k=1-3p_k$. For any such $\sigma$ and any real vector $q$, under that equality, `permutation_pairing` proves that at least one of $q_0q_1=q_2q_3$, $q_0q_2=q_1q_3$ or $q_0q_3=q_1q_2$ holds. For the fixed `point`, the hypothesis-free lemma `point_pairings` negates all three equalities; each supposed equality would make $\sqrt5$ rational. Consequently `point_not_product` excludes `ProductForm` for this point for every permutation $\sigma$.
4. **Contradiction.** Assuming `claim` supplies a permutation $\sigma$ and a representation of every point in `InRegion`; applying that assertion to `point` using `density_region` contradicts `point_not_product σ`. This is `result`.

## Falsifier

The refutation would miss the conjecture if its density matrices, classical version or face centres differed from the source's. Here:

- `InRegion` uses positive semidefinite trace-one complex matrices. Their diagonals are real, so recording the real parts does not weaken the prescribed classical version. For Hermitian matrices $A,B$, $\langle Au,Bv\rangle=\langle u,ABv\rangle$; hence $AB=0$ is equivalent to orthogonal ranges, which in finite dimension are their supports.
- The reused `RebitExclusionDistance.target j` is exactly the function taking value zero at coordinate $j$ and $1/3$ elsewhere. Its use imports these face centres, not a restriction to real quantum states.
- `ProductForm` keeps both interval conditions $a,b\in[0,1]$. The proof excludes every permutation of the centres using the same fixed point and uses pure rank-one states, so neither a labelling convention nor allowing mixed states accounts for the refutation.

## Evidence

The canonical source is `D5/S3/Quantum/Measurements/ThreeDistinguishabilityProductRefutation.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurements/ThreeDistinguishabilityProductRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:e91502c115e91d9c2b982b1afb1bd7838354abfb5c58cd866466e28904cd81b9`;
- `claim`: `sha256:179ea3089f56c0284649285da758e58d08dce86cd36f39c940441b8797a876d6`.

## Triage

Tier 1 conjecture of a 2019 paper, retained in arXiv v3, preregistered in issue #25867 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** there is no permutation of the four face centres for which every nonnegative real four-vector of sum one admitting three positive semidefinite trace-one complex $4\times4$ matrices with pairwise zero products and that common diagonal has the product representation with two parameters in $[0,1]$.

**Computed, not formalized:** None.

**Argued, not formalized**:

- *Mechanism and missing structure.* For a nonnegative four-vector $p$ of sum one with $p_k\le1/3$, the residual coordinates $q_k=1-3p_k$ are nonnegative and sum to one. In a chosen labelling these are exactly the barycentric weights of $p$, since $p_{\sigma(j)}=(1-w_j)/3$. Arrange them as $Q=\left(\begin{smallmatrix}q_{\sigma(0)}&q_{\sigma(1)}\\q_{\sigma(2)}&q_{\sigma(3)}\end{smallmatrix}\right)$. Product form is equivalent to $\det Q=0$: necessity is multiplication of the four product weights; conversely, set $a=Q_{00}+Q_{01}$ and $b=Q_{00}+Q_{10}$. Then $Q_{00}-ab=Q_{00}Q_{11}-Q_{01}Q_{10}=0$, and the row and column sums give the other three entries $a(1-b)$, $(1-a)b$ and $(1-a)(1-b)$. Nonnegativity gives $a,b\in[0,1]$, including zero rows or columns. Thus product form adds independence of two binary indices to the residual weights. The constructed orthogonal states satisfy no such equal-product pairing, as `point_pairings` and `point_not_product` establish for the fixed point and every labelling; orthogonality does not supply that independence.
- *Interior and pure states.* The elementary bounds $2<\sqrt5<9/4$ put every coordinate of the fixed `point` strictly between zero and $1/3$, so it is interior to both the simplex and the bounding tetrahedron. Restricting the conjecture to pure states still retains this witness: `density_region`, with no additional hypotheses, uses precisely the rank-one matrices displayed in the route. A boundary-only correction therefore does not address the obstruction.
- *Nearby statements that survive.* For any three positive semidefinite trace-one matrices with pairwise zero products, each eigenvalue is at most one and their ranges are orthogonal; their sum is therefore at most the identity. A common diagonal $p$ consequently satisfies $3p_k\le1$, preserving the source's necessary permutohedron bound (Section III.A, lines 345–359). Nonempty product examples also remain: the uniform diagonal is realized by any three columns of the four-dimensional Fourier unitary and has $a=b=1/2$; each face centre is realized by the three columns of the three-dimensional Fourier unitary embedded on its nonzero coordinates and has a product representation with endpoint parameters. In each construction the geometric sum of distinct Fourier phases is zero and each nonzero squared modulus is the reciprocal of the support size. These examples do not establish sufficiency of product form for arbitrary parameters.
- *Effect on the paper and remaining questions.* Eq. (30) is not a necessary condition for membership, even allowing a different labelling for each point, because the same fixed `point` is excluded for every permutation by `point_not_product`. The complete-region interpretation of Fig. 2(c) and the conjectural curves in the numerical-evidence figure of Appendix C.3 cannot be retained. The separate inclusion and exclusion arguments of Appendix C.1–2 do not use Eq. (30); this settlement does not refute them or the paper's channel results. A full description of $\mathcal A^3_4$, and whether the product ansatz is sufficient for membership throughout its parameter square, remain open here.

## ASSUMED-UNVERIFIED

The bounded literature check in #25867 does not establish exhaustive worldwide novelty or priority. The seven citing works, their reported lack of a settlement, the INSPIRE citation listing and the preregistration's repository-search readings were not independently reproduced. The source's numerical region reconstruction and plotted cross sections in Appendix C.3 were not reproduced.

The statements under “Argued, not formalized” are not additional conclusions of `result`. The operational identification with perfect distinguishability and the support and diagonal interpretations in “Falsifier” are mathematical translations of the matrix formulation, not separate formalized equivalences in this module. The product-weight factorization argument, strict interior bounds, general permutohedron argument, Fourier examples and discussion of the paper's dependencies have no separate declarations here. The source's independent inclusion, exclusion and channel results are not certified by this settlement. No full-region characterization or general sufficiency theorem for product form is claimed.
