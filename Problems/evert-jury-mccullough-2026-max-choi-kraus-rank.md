---
slug: evert-jury-mccullough-2026-max-choi-kraus-rank
bibkey: evertjurymccullough2026completely
doi: 10.48550/arXiv.2607.13251
url: https://arxiv.org/pdf/2607.13251v1#page=22
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.result
---

# Maximum Choi–Kraus rank of matrix products with units

## Problem

Eric Evert, Michael T. Jury and Scott McCullough pose one Question 1 in §5.3, printed page 22. It has two clauses.

1. “What is the maximum Choi-Kraus rank of a jcp product with a left unit?”
2. “What is the maximum Choi-Kraus rank of a jcp product with a unit?”

For each positive integer $n$, take complex bilinear products $\Phi\colon M_n(\mathbb C)\times M_n(\mathbb C)\to M_n(\mathbb C)$. Joint complete positivity requires the block matrix $[\Phi(A_{ij},B_{st})]_{(i,s),(j,t)}$ to be positive semidefinite for every positive block size $\ell$ and every pair of positive semidefinite inputs $A,B\in M_\ell(M_n(\mathbb C))$. The length is the minimum number of rectangular matrices $V_k\colon\mathbb C^n\to\mathbb C^n\otimes\mathbb C^n$ in the formula $\Phi(A,B)=\sum_k V_k^*(A\otimes B)V_k$ for all $A,B$. The formal infimum uses extended natural numbers and allows length zero. The left-unit identity is $\Phi(L,Y)=Y$ for every $Y$. The second clause requires a single $T$ satisfying $\Phi(T,Y)=Y$ and $\Phi(X,T)=X$ for every $X,Y$. All three matrix variables range over the full complex matrix space. [Author question](https://arxiv.org/pdf/2607.13251v1#page=22) · [Choi and Kraus conventions](https://arxiv.org/pdf/2607.13251v1#page=4)

## Motivation

The rectangular coefficient bound in Theorem 2.1 gives a uniform cap of $n^3$. Lemma 5.5 supplies full-rank commutative examples without requiring any unit. Example 5.10 gives a weighted Schur product with an indefinite common unit, while Lemmas 5.8 and 5.11 describe uniqueness and restrictions for positive units. [Full-rank commutative products](https://arxiv.org/pdf/2607.13251v1#page=17) · [Unit definitions and uniqueness](https://arxiv.org/pdf/2607.13251v1#page=18) · [Weighted Schur example and PSD unit restrictions](https://arxiv.org/pdf/2607.13251v1#page=19)

## Gap

The gap is whether full Choi rank $n^3$ can coexist with a left unit or with a common two-sided unit in every positive dimension. The first question asks for attainment under the left identity alone. One full-rank product satisfying both identities with the same unit would give attainment in both classes.

The authors' arXiv record lists one version, which poses both questions. The five Crossref title results contained no matching journal record. The sole citing work indexed by OpenAlex concerns the broader completely positive convolution framework and gives neither maximum. The literature finding is limited to these records. [Author record](https://arxiv.org/abs/2607.13251v1) · [Crossref title results](https://api.crossref.org/works?query.title=Completely%20Positive%20Matrix%20Products&rows=5) · [OpenAlex citation index](https://api.openalex.org/works?filter=cites:W7169633006) · [Citing preprint](https://arxiv.org/abs/2609.26755v1)

## Route

For any jointly completely positive product, testing the amplification at $\ell=n$ on matrix-unit block dyads gives a positive semidefinite Choi matrix. A simultaneous reindexing identifies this with the output-first Choi matrix of the linearization on the tensor input space. The rectangular Choi factorization then gives a representation with $n^3$ coefficients. For any length $N$, the Choi matrix is a Gram factorization by the flattened rectangular coefficients and has rank at most $N$. A positive-definite Choi matrix therefore forces the minimum to equal $n^3$. The Kraus formula gives the original all-level amplification predicate by positive semidefinite sandwiches.

For $n\geq2$, put $J$ equal to the all-ones matrix, $P=I+J$, $T=J-I/2$, and $H=(2n-1)I-J$. The product
$$
\Phi(A,B)=P\circ A\circ B+\operatorname{Tr}(HA)\operatorname{Tr}(HB)I
$$
uses entrywise multiplication in the first term. The entrywise identity $P\circ T=J$ and the equality $\operatorname{Tr}(HT)=0$ preserve both unit identities. The weighted Schur Choi contribution is positive semidefinite. The added Choi contribution is $H^{\mathsf T}\otimes H^{\mathsf T}\otimes I$ and is positive definite because the eigenvalues of $H$ are $n-1$ on the constant direction and $2n-1$ on its orthogonal complement. For $n=1$, ordinary scalar multiplication has unit $1$ and Choi rank $1$. The two-sided attainer also serves as a left-unit attainer.

## Falsifier

A qualifying square product with minimum length exceeding $n^3$ in any positive dimension would disprove the corresponding upper bound. A proof that every product in one of the two classes has smaller minimum length in a fixed positive dimension would disprove that attainment clause. The proposed witness can be tested by either unit identity on matrix units, by its Choi form, and by the one-dimensional case.

## Evidence

The Lean declaration `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.result` proves both bounds and both attainments for every $n\geq1$ with input and output size $n$. It uses the original joint block test with independently quantified positive semidefinite inputs and the extended-natural infimum over admissible rectangular Kraus lengths, including zero. The left-unit clause quantifies over unrestricted complex matrices, and the two-sided clause uses one unrestricted matrix for both identities. The proof uses rectangular Choi reconstruction and factorization from the attributed Physlib port in `FiniteKrausRepresentation` and identities from pinned Mathlib.

Evert, Jury and McCullough posed Question 1 and provided the weighted Schur example. The full-rank unit-preserving construction is due to the `codex-search-a-r420` search seat (flight `239350cace4a88318b136f9d`). The Codex CLI research seat (flight `ca2aa9724d4453e01487da3f`, with repository prior exposure) checked it. Claude Code (session `07b67e50-10a4-41b3-9622-660f37c654a5`) orchestrated that research. A separate Codex CLI source qualification (flight `6b025c6c7ab053a2e5a8b5da`) established source and convention correspondence. The Codex CLI Lean producer (flight `6b025f8f5a9a4c8fcf9f0c9a`) supplied the kernel-checked proof. [Credit and exact target](https://github.com/the-omega-institute/trureturing/issues/29866)

The earlier linked experiment records exact rational checks at $n=1,2,3$ for the witness and separately checks Example 5.10. Its finite readings are supplementary to the all-dimensional Lean result. [Recorded experiment](https://github.com/the-omega-institute/trureturing-experiments/tree/24d25aa2ecfad1bdf71c015f0655bab9822eeec4/docs/reports/ejm2607-max-choi-kraus-rank)

## Triage

### What the settlement shows

- **Proved in Lean.** Both maxima are $n^3$ for every $n\geq1$. The upper bound actually needs only joint complete positivity. Full Choi rank is compatible with a single common unrestricted unit. At $n=1$ the proof uses the scalar product and unit $1$.
- **Spectrum of the exhibited unit, by the explicit formula.** For $n\geq2$, $T$ has the positive eigenvalue $n-1/2$ on the constant vector and the negative eigenvalue $-1/2$ on its orthogonal complement. This spectrum calculation is outside the Lean endpoint.
- **Paper consequence for a positive semidefinite left unit, outside the Lean endpoint.** If $L\succeq0$ has rank $r$, write it as a sum of $r$ orthogonal vector dyads with eigenvalue weights absorbed into the vectors. Contracting any coefficient $V_k$ along each such vector in its first input gives a Kraus operator for the identity map. Lemma 5.12 forces each contraction to be scalar times $I$. Thus $r$ independent input slices have one scalar degree of freedom each, and the remaining $n-r$ slices each have $n^2$ degrees of freedom. Remark 2.2 bounds the minimum length by $(n-r)n^2+r$. This is sharp for a fixed rank $1\le r\le n$: take $L$ to be the rank-$r$ coordinate projection, use the $r$ coefficients $y\mapsto e_i\otimes y/\sqrt r$ on the supported coordinates, and include every elementary coefficient on the complementary first-input slices. The contractions give the identity and the coefficients are independent. Thus a PSD left unit rules out full rank for $n>1$. A positive-definite left unit allows at most $n$, attained by $\Phi(A,B)=\operatorname{Tr}(A)B$ with $L=I/n$.
- **Paper consequence for a common positive semidefinite unit, outside the Lean endpoint.** A common unit is unique even as a left unit (Lemma 5.8). If its rank exceeded one, Lemma 5.11(ii) would supply distinct rank-one PSD left units. A common PSD unit therefore has rank one. For a rank-one coordinate unit $e_0e_0^*$, each coefficient's contractions with $e_0$ in the first and second input are scalar multiples of $I$, by the identity-map lemma in each input order. Their shared $(0,0)$ row forces the scalars to agree. After a joint change of orthonormal basis and scaling for a general rank-one unit, the dimension bound is $1+n(n-1)^2$. With the coordinate unit, it is attained by the coefficient $e_0\mapsto e_0\otimes e_0$, $e_a\mapsto e_0\otimes e_a+e_a\otimes e_0$ for $a>0$, together with every elementary coefficient supported where both input coordinates are nonzero. Both contracted families give the identity and the coefficients are independent. In particular, a common positive-definite unit is possible only at $n=1$.
- **Source scope.** The new attainment answers Question 1 as worded. Lemmas 5.8, 5.11 and 5.12 and Theorem 5.13 have their original hypotheses. The right-hand PSD inference uses input swap and the identity-map lemma, whose argument requires a PSD dyad decomposition. No inference from it is made for arbitrary right units using the unqualified wording of Remark 5.14. Separability, associativity, and trace normalization play no role in the two maxima. The Lean construction establishes strict Choi positivity. The quantitative inequality $C_\Phi\succeq(n-1)^2I$ lies outside the checked declarations. [PSD unit restrictions](https://arxiv.org/pdf/2607.13251v1#page=19) · [Identity-map lemma and PSD unit criterion](https://arxiv.org/pdf/2607.13251v1#page=20)

## ASSUMED-UNVERIFIED

Literature completeness, global priority, and any unindexed journal treatment remain unverified. The PSD-unit consequences above are mathematical derivations from the cited Choi and unit lemmas. Their full statements have no kernel-checked application in this delivery.
