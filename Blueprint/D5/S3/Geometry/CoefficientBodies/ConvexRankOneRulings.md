# Convex coefficient bodies and transverse rank-one pairs

## Abstract

The whole pointwise coefficient body has a common rank-one factor exactly when it has no full two-column-rank lift.

**Definition 1.1 (The original four labels).**

Lean statement: `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.Label`

*Formalization.* `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.Label` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constructors zero, one, three and B represent the labels 0, 1, 3 and B in that order. They are four distinct labels; three is not the third numeric array index.

**Definition 1.2 (Real rectangular coefficient matrices).**

Lean statement: `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.Coeff`

*Formalization.* `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.Coeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coeff(d) is Matrix Label (Fin d) Real. The Fin 1 index 0 denotes radical column 1. The Fin 2 indices 0 and 1 denote radical columns 1 and 2, respectively. No square-matrix or complex-scalar substitution is made.

**Definition 1.3 (Zero-sum label vectors).**

Lean statement: `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.H`

*Formalization.* `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

H consists of all real vectors c on the four labels with sum_y c_y = 0. It contains zero and also the nonzero vector with coordinates (1,-1,0,0).

**Definition 1.4 (All coefficient column sums vanish).**

Lean statement: `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.ZeroSum`

*Formalization.* `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.ZeroSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ZeroSum(A) requires sum_y A[y,j] = 0 separately for every radical coordinate j. It imposes no sign condition on a coefficient entry.

**Definition 1.5 (The literal pointwise feasibility body).**

Lean statement: `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.body`

*Formalization.* `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.body` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an arbitrary type X of points, b_y : X -> Real and r_j : X -> Real, body(b,r) is exactly {A | all column sums are zero AND for every label y and every point x, b_y(x) + sum_j A[y,j] r_j(x) >= 0}. X can be empty or infinite. There is no sampling, finite catalogue, almost-everywhere replacement, uniform positivity, closure or nonemptiness premise.

**Definition 1.6 (Every real convex-combination parameter).**

Lean statement: `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.blend`

*Formalization.* `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.blend` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

blend(theta,A,B) is theta times A plus (1-theta) times B. The algebraic identity holds for every real theta; the rank and feasibility criteria quantify over every strict parameter 0 < theta < 1.

**Definition 1.7 (Actual two-by-two submatrix determinant).**

Lean statement: `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.minor`

*Formalization.* `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.minor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

minor(A,i,k,j,l) is the determinant of the submatrix with ordered rows (i,k) and columns (j,l). This is the actual Mathlib determinant. Its expansion is A[i,j] A[k,l] - A[i,l] A[k,j]. The identity also holds when indices repeat; the source's two-row sets and distinct columns are included.

**Definition 1.8 (Coordinates of the exterior product).**

Lean statement: `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.wedge`

*Formalization.* `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.wedge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

wedge(u,s,i,k) = u_i s_k - u_k s_i. Parallel(u,s) means every such coordinate vanishes. Its negation is exactly nonvanishing of the exterior product, rather than a chosen nonzero coordinate imposed in advance.

**Definition 1.9 (Vanishing of all wedge coordinates).**

Lean statement: `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.Parallel`

*Formalization.* `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.Parallel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a nonzero u, Parallel(u,s) is equivalent to s = a*u for some real a. The scalar a may be zero; only when the vector s is also nonzero is a forced nonzero.

**Definition 1.10 (Independence in both factor spaces).**

Lean statement: `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.Transverse`

*Formalization.* `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.Transverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transverse(u,s,v,t) means that u and s are not parallel in label space and v and t are not parallel in radical-coordinate space. Both factors must be independent; one independent pair alone does not suffice.

**Definition 1.11 (One fixed factor across the entire family).**

Lean statement: `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.Rulings`

*Formalization.* `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.Rulings` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Rulings(C) is the disjunction: some fixed nonzero c in H represents every A in C as c z^T, or some fixed nonzero w in Real^2 represents every A in C as v w^T with v in H. The quantified family C is arbitrary. Zero matrices are allowed through z=0 or v=0, and the fixed factor is always nonzero. This predicate is a conclusion, never a hypothesis of the classification direction.

**Definition 1.12 (An intrinsic nonzero rank-one pair).**

Lean statement: `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.TransversePair`

*Formalization.* `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.TransversePair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The predicate requires both endpoint matrices to be nonzero of actual Matrix.rank one, and gives nonzero label factors u,s in H and nonzero coordinate factors v,t with A=u v^T, B=s t^T and Transverse(u,s,v,t). Its mathematical value does not depend on a choice of factors.

**Theorem 1.13 (The complete one-column, whole-family and transverse-pair interface).**

$$\forall X \in Type,\; \forall b \in Label \to \left(X \to \mathbb{R}\right),\; \forall r1 \in \operatorname{Fin}\left(1\right) \to \left(X \to \mathbb{R}\right),\; \forall r2 \in \operatorname{Fin}\left(2\right) \to \left(X \to \mathbb{R}\right),\; \operatorname{Convex}\left(\mathbb{R}, \operatorname{body}\left(b, r1\right)\right) \land \left(\operatorname{Convex}\left(\mathbb{R}, \operatorname{body}\left(b, r2\right)\right) \land \left(\left(\left(\exists A \in \operatorname{Coeff}\left(1\right),\; A \in \operatorname{body}\left(b, r1\right) \land \operatorname{rank}\left(A\right) = 1\right) \Leftrightarrow \left(\neg \operatorname{body}\left(b, r1\right) \subseteq \left\{0\right\}\right)\right) \land \left(\left(\left(\neg \left(\exists A \in \operatorname{Coeff}\left(2\right),\; A \in \operatorname{body}\left(b, r2\right) \land \operatorname{rank}\left(A\right) = 2\right)\right) \Leftrightarrow \operatorname{Rulings}\left(\operatorname{body}\left(b, r2\right)\right)\right) \land \left(\left(\left(\exists A \in \operatorname{Coeff}\left(2\right),\; A \in \operatorname{body}\left(b, r2\right) \land \operatorname{rank}\left(A\right) = 2\right) \Leftrightarrow \left(\neg \operatorname{Rulings}\left(\operatorname{body}\left(b, r2\right)\right)\right)\right) \land \left(\left(\left(\exists A \in \operatorname{Coeff}\left(2\right),\; A \in \operatorname{body}\left(b, r2\right) \land \operatorname{rank}\left(A\right) = 2\right) \Leftrightarrow \left(\exists A \in \operatorname{Coeff}\left(2\right),\; A \in \operatorname{body}\left(b, r2\right) \land \left(\exists B \in \operatorname{Coeff}\left(2\right),\; B \in \operatorname{body}\left(b, r2\right) \land \left(\exists i \in Label,\; \exists k \in Label,\; \exists j \in \operatorname{Fin}\left(2\right),\; \exists l \in \operatorname{Fin}\left(2\right),\; \operatorname{minor}\left(\operatorname{blend}\left(\frac{1}{2}, A, B\right), i, k, j, l\right) \ne 0\right)\right)\right)\right) \land \left(\left(\left(\forall A \in \operatorname{Coeff}\left(2\right),\; A \in \operatorname{body}\left(b, r2\right) \Rightarrow \left(\forall B \in \operatorname{Coeff}\left(2\right),\; B \in \operatorname{body}\left(b, r2\right) \Rightarrow \left(\forall i \in Label,\; \forall k \in Label,\; \forall j \in \operatorname{Fin}\left(2\right),\; \forall l \in \operatorname{Fin}\left(2\right),\; \operatorname{minor}\left(\operatorname{blend}\left(\frac{1}{2}, A, B\right), i, k, j, l\right) = 0\right)\right)\right) \Rightarrow \operatorname{Rulings}\left(\operatorname{body}\left(b, r2\right)\right)\right) \land \left(\left(\forall A \in \operatorname{Coeff}\left(2\right),\; \operatorname{ZeroSum}\left(A\right) \Rightarrow \left(A \ne 0 \Rightarrow \left(\operatorname{rank}\left(A\right) = 1 \Rightarrow \left(\exists u \in Label \to \mathbb{R},\; u \in H \land \left(\exists v \in \operatorname{Fin}\left(2\right) \to \mathbb{R},\; u \ne 0 \land \left(v \ne 0 \land A = \operatorname{vecMulVec}\left(u, v\right)\right)\right)\right)\right)\right)\right) \land \left(\left(\forall u \in Label \to \mathbb{R},\; \forall s \in Label \to \mathbb{R},\; \forall v \in \operatorname{Fin}\left(2\right) \to \mathbb{R},\; \forall t \in \operatorname{Fin}\left(2\right) \to \mathbb{R},\; \forall theta \in \mathbb{R},\; \forall i \in Label,\; \forall k \in Label,\; \forall j \in \operatorname{Fin}\left(2\right),\; \forall l \in \operatorname{Fin}\left(2\right),\; \operatorname{minor}\left(\operatorname{blend}\left(theta, \operatorname{vecMulVec}\left(u, v\right), \operatorname{vecMulVec}\left(s, t\right)\right), i, k, j, l\right) = theta \cdot \left(1 - theta\right) \cdot \operatorname{wedge}\left(u, s, i, k\right) \cdot \operatorname{wedge}\left(v, t, j, l\right)\right) \land \left(\left(\forall u \in Label \to \mathbb{R},\; \forall s \in Label \to \mathbb{R},\; \forall v \in \operatorname{Fin}\left(2\right) \to \mathbb{R},\; \forall t \in \operatorname{Fin}\left(2\right) \to \mathbb{R},\; \forall theta \in \mathbb{R},\; 0 < theta \Rightarrow \left(theta < 1 \Rightarrow \left(\operatorname{rank}\left(\operatorname{blend}\left(theta, \operatorname{vecMulVec}\left(u, v\right), \operatorname{vecMulVec}\left(s, t\right)\right)\right) = 2 \Leftrightarrow \operatorname{Transverse}\left(u, s, v, t\right)\right)\right)\right) \land \left(\left(\forall u \in Label \to \mathbb{R},\; \forall s \in Label \to \mathbb{R},\; \forall u2 \in Label \to \mathbb{R},\; \forall s2 \in Label \to \mathbb{R},\; \forall v \in \operatorname{Fin}\left(2\right) \to \mathbb{R},\; \forall t \in \operatorname{Fin}\left(2\right) \to \mathbb{R},\; \forall v2 \in \operatorname{Fin}\left(2\right) \to \mathbb{R},\; \forall t2 \in \operatorname{Fin}\left(2\right) \to \mathbb{R},\; \operatorname{vecMulVec}\left(u, v\right) = \operatorname{vecMulVec}\left(u2, v2\right) \Rightarrow \left(\operatorname{vecMulVec}\left(s, t\right) = \operatorname{vecMulVec}\left(s2, t2\right) \Rightarrow \left(\operatorname{Transverse}\left(u, s, v, t\right) \Leftrightarrow \operatorname{Transverse}\left(u2, s2, v2, t2\right)\right)\right)\right) \land \left(\left(\forall A \in \operatorname{Coeff}\left(2\right),\; A \in \operatorname{body}\left(b, r2\right) \Rightarrow \left(\forall B \in \operatorname{Coeff}\left(2\right),\; B \in \operatorname{body}\left(b, r2\right) \Rightarrow \left(\forall theta \in \mathbb{R},\; 0 < theta \Rightarrow \left(theta < 1 \Rightarrow \left(\operatorname{blend}\left(theta, A, B\right) \in \operatorname{body}\left(b, r2\right) \land \left(A \ne 0 \Rightarrow \left(B \ne 0 \Rightarrow \left(\operatorname{rank}\left(A\right) = 1 \Rightarrow \left(\operatorname{rank}\left(B\right) = 1 \Rightarrow \left(\operatorname{rank}\left(\operatorname{blend}\left(theta, A, B\right)\right) = 2 \Leftrightarrow \operatorname{TransversePair}\left(A, B\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \land \left(\left(\left(\forall A \in \operatorname{Coeff}\left(2\right),\; A \in \operatorname{body}\left(b, r2\right) \Rightarrow \operatorname{rank}\left(A\right) \le 1\right) \Rightarrow \left(\left(\neg \left(\exists A \in \operatorname{Coeff}\left(2\right),\; A \in \operatorname{body}\left(b, r2\right) \land \left(\exists B \in \operatorname{Coeff}\left(2\right),\; B \in \operatorname{body}\left(b, r2\right) \land \left(\exists theta \in \mathbb{R},\; 0 < theta \land \left(theta < 1 \land \operatorname{rank}\left(\operatorname{blend}\left(theta, A, B\right)\right) = 2\right)\right)\right)\right)\right) \land \left(\left(\neg \left(\exists A \in \operatorname{Coeff}\left(2\right),\; A \in \operatorname{body}\left(b, r2\right) \land \left(\exists B \in \operatorname{Coeff}\left(2\right),\; B \in \operatorname{body}\left(b, r2\right) \land \operatorname{TransversePair}\left(A, B\right)\right)\right)\right) \land \left(\left(\left(\exists A \in \operatorname{Coeff}\left(2\right),\; A \in \operatorname{body}\left(b, r2\right) \land \left(\exists B \in \operatorname{Coeff}\left(2\right),\; B \in \operatorname{body}\left(b, r2\right) \land \left(\exists theta \in \mathbb{R},\; 0 < theta \land \left(theta < 1 \land \operatorname{rank}\left(\operatorname{blend}\left(theta, A, B\right)\right) = 2\right)\right)\right)\right) \Leftrightarrow \left(\exists A \in \operatorname{Coeff}\left(2\right),\; A \in \operatorname{body}\left(b, r2\right) \land \left(\exists B \in \operatorname{Coeff}\left(2\right),\; B \in \operatorname{body}\left(b, r2\right) \land \operatorname{TransversePair}\left(A, B\right)\right)\right)\right) \land \operatorname{Rulings}\left(\operatorname{body}\left(b, r2\right)\right)\right)\right)\right)\right) \land \left(\left(\forall C \in \operatorname{Set}\left(\operatorname{Coeff}\left(2\right)\right),\; \operatorname{Convex}\left(\mathbb{R}, C\right) \Rightarrow \left(\left(\forall A \in \operatorname{Coeff}\left(2\right),\; A \in C \Rightarrow \operatorname{ZeroSum}\left(A\right)\right) \Rightarrow \left(\left(\forall A \in \operatorname{Coeff}\left(2\right),\; A \in C \Rightarrow \operatorname{rank}\left(A\right) \le 1\right) \Leftrightarrow \operatorname{Rulings}\left(C\right)\right)\right)\right) \land \left(\forall A \in \operatorname{Coeff}\left(2\right),\; \operatorname{rank}\left(A\right) = 2 \Leftrightarrow \left(\exists i \in Label,\; \exists k \in Label,\; \exists j \in \operatorname{Fin}\left(2\right),\; \exists l \in \operatorname{Fin}\left(2\right),\; \operatorname{minor}\left(A, i, k, j, l\right) \ne 0\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be any point type, b any four real functions on X, r1 any one-coordinate radical family and r2 any two-coordinate radical family. The result includes convexity for both literal bodies. All conclusions below are conjuncts of one statement. In particular, the arbitrary-family classification is also stated for every convex C of real 4 by 2 matrices satisfying the zero-column-sum equations, independently of the coefficient-body specialization.

For one column, a feasible rank-one matrix exists exactly when the body is not contained in the singleton zero. Nonzero entries give positive actual rank by the pinned nonzero-determinant and submatrix-rank theorems, while the width bound is one. This proves both directions of the rank-three coefficient test, even when the body is empty or all-zero.

For two columns, absence of a feasible rank-two matrix is equivalent to Rulings(body). Its negation says a rank-two feasible lift exists exactly when the whole body escapes both fixed-factor rulings. The converse inclusion-to-deficiency direction uses Matrix.rank_vecMulVec_le. The classification direction never assumes a ruling, a prescribed factor, finiteness of the family, or a catalogue of endpoints.

The common-factor derivation first chooses a nonzero A0=u v^T if one exists. Otherwise a fixed nonzero c=(1,-1,0,0) supplies the first ruling, including the empty family. For each nonzero member, the dimension-at-most-one range theorem supplies factors; the column-sum equation at a nonzero coordinate puts the label factor in H. Midpoint rank at most one implies that each pair shares at least one factor direction. If every member has label factor along u, the first ruling holds. Otherwise choose B=s t^T outside that ruling. Pair compatibility forces t to be a nonzero scalar multiple of v; absorb that scalar into s. For arbitrary D=p q^T, if q were not parallel to v, compatibility with A0 and with B would force both u and s along the nonzero p. That contradicts the choice of B. Thus q is parallel to v for every D and the second ruling holds. Zero members use zero variable factors. This is a proof about the whole family rather than a pairwise disjunction promoted to a uniform conclusion without justification.

An exact rank/minor interface is included: for every real 4 by 2 matrix, actual Matrix.rank equals two if and only if some two-by-two minor is nonzero. The proof uses the pinned width bound and range dimension theorem. In the zero-minor direction a nonzero pivot reconstructs an outer product; zero matrices are handled separately. Consequently the statement is not a determinant-defined rank proxy. It also proves that a full-rank feasible matrix exists exactly when some feasible midpoint has a nonzero minor: the forward direction uses A=B, and the reverse direction uses convexity. If every feasible midpoint has every minor zero, the whole body lies in a common ruling.

For every nonzero zero-sum actual rank-one endpoint, the statement supplies A=u v^T with nonzero u in H and nonzero v. For every real theta and all row and column choices, the determinant of theta*u v^T + (1-theta)*s t^T is theta*(1-theta)*(u_i s_k-u_k s_i)*(v_j t_l-v_l t_j). The pure quadratic terms vanish. For every 0 < theta < 1, the positive scalar theta*(1-theta) and the exact rank/minor interface give actual rank two if and only if both wedge factors are nonzero. These factor and determinant steps are reused interfaces and algebraic normalization, not claimed new mathematical content.

Factorization independence is stronger than nonzero-rescaling independence: whenever u v^T=u' v'^T and s t^T=s' t'^T, Transverse(u,s,v,t) if and only if Transverse(u',s',v',t'). Apply the strict rank criterion to the same midpoint in the two representations. The usual changes (u,v)->(a*u,a^(-1)*v), (s,t)->(c*s,c^(-1)*t), for nonzero a,c, preserve the endpoint matrices and are included. The rank criterion remains true for degenerate factors; the intrinsic pair predicate separately retains all original nonzero and rank-one endpoint requirements.

For any feasible A,B and every strict theta, the combination is feasible. If both endpoints are nonzero and individually rank one, its actual rank is two exactly when TransversePair(A,B). Therefore any transverse feasible rank-one pair supplies a full-column-rank lift for every strict parameter, with no change to the pointwise inequalities.

Under the separate hypothesis that every feasible matrix has rank at most one, there is no rank-two strict combination and there is no transverse pair. The statement explicitly records both negations and their equivalence, then supplies the common ruling. Thus the second paragraph of the pairwise criterion is a conditional exclusion: its two existence sides are both false. No equivalence between arbitrary convex-body rank-two existence and existence of a transverse rank-one pair is asserted. A convex body can already contain rank-two matrices without containing any nonzero rank-one endpoint.

For the original radical application, take X to be the full set G of chosen representatives, W to be the fixed candidate span, Q to be the baseline target, and evaluation to be the inclusion of W into real functions on X. Let T:W -> Q and S:Q -> W be real linear maps with T(S(q))=q. Write R=ker T and choose a basis r indexed by Fin d of R. The quotient labels f_y satisfy sum_y f_y=oneQ; require S(oneQ)=oneW and evaluation(oneW)=1. Set b_y(x)=evaluation(S(f_y))(x) and radical_j(x)=evaluation(r_j)(x). The label map is exactly (0,1,3,B), and Fin 2 coordinates 0 and 1 are exactly radical columns 1 and 2. Substitution into body gives P_u literally, with every original pointwise inequality and zero column sum. The convex-ruling theorem needs none of these quotient hypotheses; they supply the separate interpretation of its coefficient application.

The quotient/radical bridge uses rho_y=sum_j A[y,j] r_j and u_y=S(f_y)+rho_y in W. Each T(r_j)=0, so T(u_y)=f_y. Interchanging the two finite sums and using each zero column sum gives sum_y rho_y=0; linearity of S and the unit laws give sum_y u_y=oneW and hence pointwise sum_y u_y(x)=1. The defining inequalities give nonnegativity for every y,x; together these give the simplex bounds. If the fixed trilinear form F on W satisfies F(x,y,z)=Fq(T(x),T(y),T(z)), then F(u_y,u_z,u_k)=Fq(f_y,f_z,f_k) for every triple of the original four labels: all sixty-four residuals close under this stated quotient identity. This is a conditional consequence of the fixed quotient data, not a proof that arbitrary candidate data possess that identity.

For the correction-span correspondence, the basis equivalence e:Real^d -> R sends the coefficient row A[y,-] to rho_y. Mapping the span of the rows by e gives exactly the span of the radical corrections. Matrix.rank_eq_finrank_span_row identifies actual coefficient rank with the row-span dimension; LinearEquiv.finrank_map_eq, LinearEquiv.finrank_eq and Submodule.eq_top_of_finrank_eq then give rank(A)=d if and only if the corrections span R. This includes d=0. It establishes full radical correction span and does not assert that the new labels themselves span W. The one- and two-column tests consequently detect the original required radical dimension, conditional on the fixed quotient/radical parametrization. They neither construct a feasible matrix nor certify an arbitrary partition or a physical realization.

The mathematical ingredients used directly are finrank_le_one_iff from Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition and Matrix.rank_vecMulVec_le, Matrix.rank_le_card_width, Matrix.rank_submatrix_le, Matrix.rank_of_det_ne_zero from Mathlib.LinearAlgebra.Matrix.Rank, together with the ordinary two-by-two determinant and convexity definitions. Their versions are fixed by the repository manifest. The common-factor passage across an arbitrary convex family is the repository-derived content candidate; neither novelty nor its admission is established by exposition. The source does not assert existence of a feasible transverse pair for an arbitrary partition, evaluate candidate pointwise inequalities, or settle F64, H43, SRS-20 or physical succession.

## References

- Truth anchor: `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.Coeff`
- Truth anchor: `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.H`
- Truth anchor: `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.Label`
- Truth anchor: `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.Parallel`
- Truth anchor: `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.Rulings`
- Truth anchor: `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.Transverse`
- Truth anchor: `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.TransversePair`
- Truth anchor: `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.ZeroSum`
- Truth anchor: `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.blend`
- Truth anchor: `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.body`
- Truth anchor: `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.minor`
- Truth anchor: `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.result`
- Truth anchor: `D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.wedge`
