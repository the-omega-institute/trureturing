---
slug: garcia-marco-2025-uniform-toeplitz-factorization
bibkey: garciamarco2025toeplitzfactors
doi: 10.48550/arXiv.2506.16432
url: https://arxiv.org/abs/2506.16432v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/Toeplitz/FactorizationRefutation.result
---

# The uniform single-left-multiplier Toeplitz factorization assertion

## Problem

Ignacio García-Marco, Irene Márquez-Corbella and Daniel Seco, *On the minimum number of Toeplitz factors of a matrix*, [arXiv:2506.16432v1](https://arxiv.org/abs/2506.16432v1), Section 5.2, Conjecture 5.1, original archive `Toeplitz-GMS.tex`, lines 1170–1175 (`super-conjecture`), states:

> There exists a constant C > 0 such that every matrix can be expressed as a product of an invertible matrix and C Toeplitz matrices. In particular, Toep_n ≤ Toep_n^Inv + C.

The source's introduction, equation (1), defines ordinary complex Toeplitz matrices by equality of adjacent southeast diagonal entries. Section 4 explicitly writes the left-multiplier constructions `M = P T_1 T_2` and `M = P_0 rref(M)`. The ambient matrices are complex and square, including singular matrices. The version was submitted 2025-06-19; the inspected arXiv history lists v1 only and no journal reference. The [literature note](../Library/Eigenstructure/garciamarco2025toeplitzfactors.md) gives the original definitions and neighboring questions.

The target F is the complete first assertion:

$$
\exists C\in\mathbb N,\quad 0<C\ \land\
\forall n\in\mathbb N,\quad 0<n\ \Longrightarrow\
\forall M\in\mathbb C^{n\times n},\quad
\exists P\in\mathbb C^{n\times n},\ \exists T:\operatorname{Fin}(C)\to\mathbb C^{n\times n},\quad
\operatorname{IsUnit}(P)\ \land\
(\forall k\in\operatorname{Fin}(C),\ \operatorname{Toeplitz}(T(k)))\ \land\
M=P\,\operatorname{List.prod}(\operatorname{List.ofFn}(T)).
$$

For every `i,j : Fin n` and proofs `hi : i.val + 1 < n`, `hj : j.val + 1 < n`, the Toeplitz condition is
`T i j = T ⟨i.val + 1, hi⟩ ⟨j.val + 1, hj⟩`.
This also defines the empty-size predicate; F uses positive sizes only. `IsUnit P` is actual matrix invertibility. The multiplier is on the left. `List.ofFn` orders the factors by their finite indices, and `List.prod` uses `prod([])=1`, `prod(A::L)=A*prod(L)`, with ordinary finite-sum matrix multiplication. The factor count is independent of both n and M. Exact C and at most C are equivalent by padding with the ordinary Toeplitz identity.

The result negates this entire statement. The separately printed numerical assertion J, `Toep_n ≤ Toep_n^Inv + C`, remains unsettled. No converse J ⇒ F, negation of J, or unbounded global numerical gap is established. Conjectures 5.2 and 5.3 are separate and excluded.

## Motivation

F asks whether a free invertible change of rows leaves only a bounded Toeplitz multiplication cost, uniformly in dimension, even for singular matrices. A refutation must preserve that free multiplier rather than count its coefficients. Graph row spaces expose information that row operations preserve and whose field of definition can exceed the parameter budget of any proposed fixed number of Toeplitz factors.

## Gap

[Preregistration #23130](https://github.com/the-omega-institute/trureturing/issues/23130) fixes the full F target before its Lean implementation. No exact complete settlement was identified in the bounded source and repository searches described in the literature note. The late all-state issue/PR refresh used source ID, full title, author spelling variants, factorization and invertible-reduction aliases, the MathDB page ID, and broad Toeplitz and numerical-conjecture searches. The broad searches returned 89 and 73 records respectively, without incomplete-result flags; the exact title/author target matches identify only #23130. Source-ID zero alone is insufficient: direct control #5952 concerns Robin/divisor-sum questions, while #22735 concerns GLT geometric means, #6160 history-state correlations, and #6298 a different research program. Closed, no-code and no-PR registrations are included in the exclusion rule.

The corresponding theory-volume and atom route was checked by source ID, authors and factorization content. The other theory hits concern moments, positivity and spectral matrices; no volume for F was identified. This is an uncovered formalization, not an atom coverage claim.

Parameter-count obstructions are established methodology. Ye and Lim, *Every Matrix is a Product of Toeplitz Matrices*, Found. Comput. Math. 16 (2016), 577–598, use dimension counts for generic lower bounds. Their arbitrary-matrix construction has two endpoint multipliers; it does not establish F. Standard finitely generated field bounds are documented by the Stacks Project, tags [030D](https://stacks.math.columbia.edu/tag/030D) and [030H](https://stacks.math.columbia.edu/tag/030H). No novelty of this method is claimed.

The posted MathDB submission for Conjecture 5.2 concerns quasi-Toeplitz row equivalence, explicitly excludes the factorization conjectures, and is not a premise here. A one-factor or fixed-C obstruction would not settle F.

## Route

Fix an arbitrary positive integer C. Put r=4C and n=2r=8C. Choose an r by r complex matrix X whose r² coordinates are algebraically independent over the rationals, and set

$$
M=\begin{pmatrix}I_r&X\\0&0\end{pmatrix}.
$$

The finite independent family is proved to exist from a complex transcendence basis and the cardinality of the complex numbers. Independence is not an extra premise. The witness n, X and M is chosen before any hypothetical P or tuple T.

Suppose M=PN with P invertible and N the ordered product of C ordinary Toeplitz factors. Adjacent-diagonal induction gives a representation of each positive-size Toeplitz matrix by its 2n−1 boundary diagonal coefficients, including n=1. Let K be the one intermediate field of the complex numbers generated over the rationals by all C(2n−1) coefficients of all factors. An induction on the actual ordered list product, using closure under finite sums and products, puts every entry of N in K. N itself need not be Toeplitz. No coefficient of P is counted.

Let L and R select the first and last r coordinates. From M=PN one gets

$$
P_{L,*}N_{*,L}=I_r.
$$

Thus the first-coordinate projections of the actual rows of N span the complex r-dimensional row space. The reused theorem `LinearRado.exists_nonsingular_rows` selects r actual rows for which the first block A is nonsingular. Invertibility of P also gives N=P⁻¹M, so these same rows lie in the graph of u↦uX. Their second block B consequently satisfies B=AX. Both A and B have entries in K because they are submatrices of N. Arbitrary complex row combinations are not used as K-valued coordinates.

The inclusion K→ℂ preserves determinants. The nonzero complex determinant implies that A has nonzero determinant over K. Its actual inverse over K yields X=A⁻¹B after inclusion. All r² coordinates of X therefore belong to K. Injectivity of the rational algebra map transfers their algebraic independence, giving

$$
r^2\leq\operatorname{trdeg}_{\mathbb Q}K.
$$

For the internal copies of the generators in K, their intermediate-field adjoin is proved to be all of K. The field adjoin is algebraic over their algebra adjoin; scoped algebraicity transports through the scalar-tower algebra homomorphism into K. The finitely generated bound therefore gives

$$
\operatorname{trdeg}_{\mathbb Q}K\leq C(2n-1).
$$

Field generation is not substituted for algebra generation. Finally,

$$
C(2n-1)+C=r^2,
$$

contradicting C>0. Every proposed positive uniform C fails for an actual complex square graph-block matrix. This proves the closed negation of F, without restricting P, the factors, or their complex coefficients.

## Falsifier

The resolution would fail to answer F if the source restricted its field, ranks or dimensions, placed a free endpoint on the right as well, or allowed a dimension-dependent factor count. The quoted source and left-multiplier constructions fix those distinctions. A failure of common-field closure, actual-row selection, determinant/inversion over K, algebraicity transport, or the variable-size independence construction would also break the argument; these bridges are part of the compiled proof. A surrogate row-space claim without the matrix-product bridge would be insufficient. An earlier exact settlement or another person's exact registration would invalidate the claimed research allocation; the bounded searches do not rule out every unindexed source.

## Evidence

The mathematical source is [FactorizationRefutation.lean](../D5/S3/Quantum/Matrix/Toeplitz/FactorizationRefutation.lean), with its [Blueprint](../Blueprint/D5/S3/Quantum/Matrix/Toeplitz/FactorizationRefutation.md). Its two public definitions are `IsOrdinaryToeplitz` and `claim`; its only public theorem is the designated `result : ¬ claim`. Eight private helpers are consumed by the proof. Report inclusion is not public visibility.

The canonical scoped deposit checks the root, its named utility inputs and imports: 12 modules and 448 compiled declarations, of which the root has 33 compiled records. Their axiom closures are contained in `Classical.choice`, `Quot.sound`, and `propext`. There is no new axiom, `sorry` or assumed counterexample bridge. The claim's compiled type is literally `Prop` and the result's compiled type is literally `Not claim`, with no hypotheses or universe parameters.

Canonical module pin: `sha256:8ed39f98fc5c1b34f6d13126a3008bd7eed2252f84cfce26cadc78fe302754f5`, in `Golden/Frozen/state/D5/S3/Quantum/Matrix/Toeplitz/FactorizationRefutation.lean.json`.

| Public declaration | Compiled statement identity |
| --- | --- |
| IsOrdinaryToeplitz | sha256:4cee5b1fae7452999d4d82b82892f364ac9414905c58a0d4435606a4cd34780e |
| claim | sha256:410ee667c0efe6e055e4cf93d63c0662b4b3a0d37a0fd88be6ba90cd6f6c2890 |
| result | sha256:d16774a4ec37d8c1e30a12a411796f3e2b5d504d3364922817b5a63e611c6b42 |

Direct frozen D5 owners are `LinearRado.exists_nonsingular_rows` (statement `sha256:23bd6e06ebcb67af3a4cf2f3768594c2b80cbfc336dab5e160d6263efa2463c9`) and `LiCurvatureCriterion.toeplitzMatrix` (statement `sha256:9de876ea952518e74abccdbe65aa44d6a5d77aecbb537b8295cd03948344f5c6`). Pinned Mathlib supplies transcendence-basis cardinality, algebraic-independence transfer, algebraicity, determinants and nonsingular inverses. Late source searches include private declarations; no exact complete duplicate was identified in that searched scope. This is not exhaustive Lean-ecosystem clearance.

## Triage

Tier 1: an explicitly numbered external conjecture. `theorem`; resolution kind `refuted` for F alone. Admission is the whole external open-problem resolution under #23130, conservatively classified as bind-only synthesis. No non-bind-only escape witness or novel parameter-count method is asserted.

| Declaration | Admission and actual consumers |
| --- | --- |
| IsOrdinaryToeplitz | Faithful literature definition; claim, entry_eq_boundary, toeplitz_representation, product_field |
| claim | Full literature assertion; result |
| result | Designated external F refutation; only designated-result escape-audit exemption |
| exists_independent | Private helper; result |
| generated_field_trdeg | Private helper; result |
| entry_eq_boundary | Private helper; toeplitz_representation |
| toeplitz_representation | Private helper; product_field |
| product_field | Private helper; result |
| graphMatrix | Private definition; graph_mul_blocks, graph_coordinates_mem, result |
| graph_mul_blocks | Private helper; graph_coordinates_mem |
| graph_coordinates_mem | Private helper; result |

All eleven declarations use the conservative bind-only classification. There is no additional public theorem or unused wrapper. The definitions' Describe provenance is `FromLiterature`; the refutation is `FromRepo(Source)`.

## ASSUMED-UNVERIFIED

J remains unsettled; no unbounded difference between the global Toeplitz numbers is proved. Conjectures 5.2 and 5.3 are excluded. The MathDB 368924 reading supplied with the independent source review is HTTP 200, answerCount=0 and visible no-solutions text; this does not prove global openness. The Stage B direct request to that page returned HTTP 403, so it supplies no fresh answer-count or openness evidence. The supplied Crossref/DataCite/OpenAlex checks and 79-record arXiv search were not independently replayed by the Stage B builder. The later arXiv:2609.27268v2 abstract concerns determinant recurrences; its full text has not been reviewed. No global priority claim is made.

Scoped compilation, canonical freeze and selected emission do not establish full current/delta admission. The full raw-v3 consumers do not accept scoped-v1; the known boundary is [#20682](https://github.com/the-omega-institute/trureturing/issues/20682). No scoped artifact is relabeled as full. Final independent architecture, quality and tests review, exact-head required CI, merge and first dev-push verification remain separate obligations. No solved-problem credit is claimed before those delivery conditions hold.
