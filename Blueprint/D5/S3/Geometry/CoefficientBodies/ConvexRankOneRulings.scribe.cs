using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.CoefficientBodies;

internal sealed class ConvexRankOneRulingsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The whole pointwise coefficient body has a common rank-one factor exactly when it has no full two-column-rank lift.",
        H("Convex coefficient bodies and transverse rank-one pairs"),
        Blocks(
            Entry("Label", "The original four labels", DescribeRole.Definition,
                "The constructors zero, one, three and B represent the labels 0, 1, 3 and B in that order. They are four distinct labels; three is not the third numeric array index."),
            Entry("Coeff", "Real rectangular coefficient matrices", DescribeRole.Definition,
                "Coeff(d) is Matrix Label (Fin d) Real. The Fin 1 index 0 denotes radical column 1. The Fin 2 indices 0 and 1 denote radical columns 1 and 2, respectively. No square-matrix or complex-scalar substitution is made."),
            Entry("H", "Zero-sum label vectors", DescribeRole.Definition,
                "H consists of all real vectors c on the four labels with sum_y c_y = 0. It contains zero and also the nonzero vector with coordinates (1,-1,0,0)."),
            Entry("ZeroSum", "All coefficient column sums vanish", DescribeRole.Definition,
                "ZeroSum(A) requires sum_y A[y,j] = 0 separately for every radical coordinate j. It imposes no sign condition on a coefficient entry."),
            Entry("body", "The literal pointwise feasibility body", DescribeRole.Definition,
                "For an arbitrary type X of points, b_y : X -> Real and r_j : X -> Real, body(b,r) is exactly {A | all column sums are zero AND for every label y and every point x, b_y(x) + sum_j A[y,j] r_j(x) >= 0}. X can be empty or infinite. There is no sampling, finite catalogue, almost-everywhere replacement, uniform positivity, closure or nonemptiness premise."),
            Entry("blend", "Every real convex-combination parameter", DescribeRole.Definition,
                "blend(theta,A,B) is theta times A plus (1-theta) times B. The algebraic identity holds for every real theta; the rank and feasibility criteria quantify over every strict parameter 0 < theta < 1."),
            Entry("minor", "Actual two-by-two submatrix determinant", DescribeRole.Definition,
                "minor(A,i,k,j,l) is the determinant of the submatrix with ordered rows (i,k) and columns (j,l). This is the actual Mathlib determinant. Its expansion is A[i,j] A[k,l] - A[i,l] A[k,j]. The identity also holds when indices repeat; the source's two-row sets and distinct columns are included."),
            Entry("wedge", "Coordinates of the exterior product", DescribeRole.Definition,
                "wedge(u,s,i,k) = u_i s_k - u_k s_i. Parallel(u,s) means every such coordinate vanishes. Its negation is exactly nonvanishing of the exterior product, rather than a chosen nonzero coordinate imposed in advance."),
            Entry("Parallel", "Vanishing of all wedge coordinates", DescribeRole.Definition,
                "For a nonzero u, Parallel(u,s) is equivalent to s = a*u for some real a. The scalar a may be zero; only when the vector s is also nonzero is a forced nonzero."),
            Entry("Transverse", "Independence in both factor spaces", DescribeRole.Definition,
                "Transverse(u,s,v,t) means that u and s are not parallel in label space and v and t are not parallel in radical-coordinate space. Both factors must be independent; one independent pair alone does not suffice."),
            Entry("Rulings", "One fixed factor across the entire family", DescribeRole.Definition,
                "Rulings(C) is the disjunction: some fixed nonzero c in H represents every A in C as c z^T, or some fixed nonzero w in Real^2 represents every A in C as v w^T with v in H. The quantified family C is arbitrary. Zero matrices are allowed through z=0 or v=0, and the fixed factor is always nonzero. This predicate is a conclusion, never a hypothesis of the classification direction."),
            Entry("TransversePair", "An intrinsic nonzero rank-one pair", DescribeRole.Definition,
                "The predicate requires both endpoint matrices to be nonzero of actual Matrix.rank one, and gives nonzero label factors u,s in H and nonzero coordinate factors v,t with A=u v^T, B=s t^T and Transverse(u,s,v,t). Its mathematical value does not depend on a choice of factors."),
            Describe.Lean(
                DescribeId.Create("convex-coefficient-body-complete-ruling-and-transverse-interface"),
                DeclarationHandle.Create(Owner + "result"),
                H("The complete one-column, whole-family and transverse-pair interface"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let X be any point type, b any four real functions on X, r1 any one-coordinate radical family and r2 any two-coordinate radical family. The result includes convexity for both literal bodies. All conclusions below are conjuncts of one statement. In particular, the arbitrary-family classification is also stated for every convex C of real 4 by 2 matrices satisfying the zero-column-sum equations, independently of the coefficient-body specialization.")),
                    Paragraph(Text("For one column, a feasible rank-one matrix exists exactly when the body is not contained in the singleton zero. Nonzero entries give positive actual rank by the pinned nonzero-determinant and submatrix-rank theorems, while the width bound is one. This proves both directions of the rank-three coefficient test, even when the body is empty or all-zero.")),
                    Paragraph(Text("For two columns, absence of a feasible rank-two matrix is equivalent to Rulings(body). Its negation says a rank-two feasible lift exists exactly when the whole body escapes both fixed-factor rulings. The converse inclusion-to-deficiency direction uses Matrix.rank_vecMulVec_le. The classification direction never assumes a ruling, a prescribed factor, finiteness of the family, or a catalogue of endpoints.")),
                    Paragraph(Text("The common-factor derivation first chooses a nonzero A0=u v^T if one exists. Otherwise a fixed nonzero c=(1,-1,0,0) supplies the first ruling, including the empty family. For each nonzero member, the dimension-at-most-one range theorem supplies factors; the column-sum equation at a nonzero coordinate puts the label factor in H. Midpoint rank at most one implies that each pair shares at least one factor direction. If every member has label factor along u, the first ruling holds. Otherwise choose B=s t^T outside that ruling. Pair compatibility forces t to be a nonzero scalar multiple of v; absorb that scalar into s. For arbitrary D=p q^T, if q were not parallel to v, compatibility with A0 and with B would force both u and s along the nonzero p. That contradicts the choice of B. Thus q is parallel to v for every D and the second ruling holds. Zero members use zero variable factors. This is a proof about the whole family rather than a pairwise disjunction promoted to a uniform conclusion without justification.")),
                    Paragraph(Text("An exact rank/minor interface is included: for every real 4 by 2 matrix, actual Matrix.rank equals two if and only if some two-by-two minor is nonzero. The proof uses the pinned width bound and range dimension theorem. In the zero-minor direction a nonzero pivot reconstructs an outer product; zero matrices are handled separately. Consequently the statement is not a determinant-defined rank proxy. It also proves that a full-rank feasible matrix exists exactly when some feasible midpoint has a nonzero minor: the forward direction uses A=B, and the reverse direction uses convexity. If every feasible midpoint has every minor zero, the whole body lies in a common ruling.")),
                    Paragraph(Text("For every nonzero zero-sum actual rank-one endpoint, the statement supplies A=u v^T with nonzero u in H and nonzero v. For every real theta and all row and column choices, the determinant of theta*u v^T + (1-theta)*s t^T is theta*(1-theta)*(u_i s_k-u_k s_i)*(v_j t_l-v_l t_j). The pure quadratic terms vanish. For every 0 < theta < 1, the positive scalar theta*(1-theta) and the exact rank/minor interface give actual rank two if and only if both wedge factors are nonzero. These factor and determinant steps are reused interfaces and algebraic normalization, not claimed new mathematical content.")),
                    Paragraph(Text("Factorization independence is stronger than nonzero-rescaling independence: whenever u v^T=u' v'^T and s t^T=s' t'^T, Transverse(u,s,v,t) if and only if Transverse(u',s',v',t'). Apply the strict rank criterion to the same midpoint in the two representations. The usual changes (u,v)->(a*u,a^(-1)*v), (s,t)->(c*s,c^(-1)*t), for nonzero a,c, preserve the endpoint matrices and are included. The rank criterion remains true for degenerate factors; the intrinsic pair predicate separately retains all original nonzero and rank-one endpoint requirements.")),
                    Paragraph(Text("For any feasible A,B and every strict theta, the combination is feasible. If both endpoints are nonzero and individually rank one, its actual rank is two exactly when TransversePair(A,B). Therefore any transverse feasible rank-one pair supplies a full-column-rank lift for every strict parameter, with no change to the pointwise inequalities.")),
                    Paragraph(Text("Under the separate hypothesis that every feasible matrix has rank at most one, there is no rank-two strict combination and there is no transverse pair. The statement explicitly records both negations and their equivalence, then supplies the common ruling. Thus the second paragraph of the pairwise criterion is a conditional exclusion: its two existence sides are both false. No equivalence between arbitrary convex-body rank-two existence and existence of a transverse rank-one pair is asserted. A convex body can already contain rank-two matrices without containing any nonzero rank-one endpoint.")),
                    Paragraph(Text("For the original radical application, take X to be the full set G of chosen representatives, b_y(x)=S_u(f_y)(x), and r1 or r2 to be the chosen radical basis. The label map is exactly (0,1,3,B), and the two radical coordinates are exactly columns 1 and 2. Substituting these functions into body yields P_u literally: all column sums zero and every pointwise affine inequality. No boundedness or quotient identity is needed for the convex-ruling theorem itself. To interpret coefficient rank d as realization of radical dimension d, the separate quotient/radical bridge from the coefficient parametrization is still required: T_u S_u=id, ker T_u=R_u, the r_j form a basis, S_u(1)=1 and the quotient labels sum to one. These give the partition, residual closure and correction-span correspondence in that bridge; the present result does not assume them in order to manufacture a physical realization.")),
                    Paragraph(Text("The mathematical ingredients used directly are finrank_le_one_iff from Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition and Matrix.rank_vecMulVec_le, Matrix.rank_le_card_width, Matrix.rank_submatrix_le, Matrix.rank_of_det_ne_zero from Mathlib.LinearAlgebra.Matrix.Rank, together with the ordinary two-by-two determinant and convexity definitions. Their versions are fixed by the repository manifest. The common-factor passage across an arbitrary convex family is the repository-derived content candidate; neither novelty nor its admission is established by exposition. The source does not assert existence of a feasible transverse pair for an arbitrary partition, evaluate candidate pointwise inequalities, or settle F64, H43, SRS-20 or physical succession."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string name, string title, DescribeRole role, string text) =>
        Describe.Lean(
            DescribeId.Create("convex-coefficient-body-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Owner + name),
            H(title),
            StatementSource.FromLean(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
