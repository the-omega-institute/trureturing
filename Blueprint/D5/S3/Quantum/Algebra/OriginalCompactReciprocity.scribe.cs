using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class OriginalCompactReciprocityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/OriginalCompactReciprocity.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual curve-exponential membership and the entire first-order relation on the same compact matrix action.",
        H("Original Compact-Action Reciprocity"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-curve-lie-algebra"),
                DeclarationHandle.Create(Prefix + "curveLieAlgebra"), H("The actual matrix tangent Lie algebra"),
                StatementSource.FromAuthor(CurveFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix any finite-dimensional real inner product space W and an actual subgroup G of the units of its continuous endomorphism algebra. The initially chosen inner product is auxiliary; invariance is derived from compactness. The underlying submodule of curveLieAlgebra G consists exactly of all ambient operator derivatives at zero of actual G-valued curves c with c(0)=1. The curves require the displayed ambient derivative at zero; global regularity is not part of this definition. No abstract algebra, chosen smaller representation, rank or dimension is supplied instead.")),
                    Paragraph(Text("Products of original curves prove addition of velocities, scalar reparametrization proves scalar closure, and constant conjugation preserves velocities. Differentiate the conjugation of a velocity L by a curve with velocity K. Mathlib's derivative of inversion in a normed algebra gives derivative KL-LK. Difference quotients stay in the actual velocity subspace, which is closed because it is finite dimensional. Thus the original matrix commutator closes on exactly this tangent carrier. Compactness is not needed for this construction."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("entire-quotient-relation"),
                DeclarationHandle.Create(Prefix + "fullRelation"), H("Every solution of the original equation"),
                StatementSource.FromAuthor(RelationFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For A in this actual tangent Lie algebra and x in the full W, fullRelation is the submodule image of the kernel of (K,y) maps to Kx+Ay under the product of the two canonical quotient maps by the real spans of A and x. It therefore includes all solutions and makes no selection of a compensation graph. Under Ax=0, changing representatives by real multiples of A and x leaves the equation unchanged. FullReciprocity requires both canonical projections of this entire submodule to be bijective."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-curve-exponential-membership"),
                DeclarationHandle.Create(Prefix + "mem_velocitySpace_iff_exp"), H("Original curves and all real exponentials"),
                StatementSource.FromAuthor(ExponentialFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the same arbitrary finite-dimensional real inner product space W, the same subgroup G of actual units in its continuous endomorphism algebra, and compactness of that original G, an operator K belongs to velocitySpace G exactly when for every real t an actual unit of G has value exp(t K). The forward curve needs only its ambient derivative at zero and value one there. Zero-dimensional W, zero K, zero and negative real time all remain in scope. No manifold, globally differentiable curve, Euler invertibility, equivalent norm or power-bound certificate is assumed.")),
                    Paragraph(Text("In the complete ambient endomorphism algebra, Mathlib's strict derivative of exp at zero is the identity. Apply its inverse function theorem to obtain a local inverse ell with ell(1)=0, derivative identity at one, and exp(ell(y))=y near one. Composing only the given actual curve with ell gives derivative K at zero. The native HasFDerivAt.lim rescaling theorem gives n times ell(c(t/n)) tending to t K. Continuity of exp and exp_nsmul turn this into the exact limit c(t/n)^n tending to exp(t K). The value image of the original compact unit subgroup is compact and closed in the ambient algebra; every sampled power is an actual group element. Closedness therefore supplies an actual unit of G at the limit.")),
                    Paragraph(Text("For the reverse implication choose the supplied actual units at each time. Unit and subgroup extensionality give the identity at zero; their ambient values are exactly the exponential curve, whose derivative there is K. The proof does not use an unproved Banach-algebra logarithm API or a Lie-group structure on the closed subgroup. This equivalence is used by the original identity-component consumer below; it is not a claim of new analytic machinery or of completion of Theorem 5.1."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-dimension-three"),
                DeclarationHandle.Create(Prefix + "finrank_eq_three"), H("Both original dimensions are three"),
                StatementSource.FromAuthor(DimensionFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume only that the original subgroup is compact and that A and x are nonzero, Ax=0, and FullReciprocity holds. Then the real dimensions of the original W and its actual curve Lie algebra are both three. Nontriviality of W follows from the nonzero witness; all finite dimensions remain in the quantified domain. There is no irreducibility, transitivity, centralizer, rank, dimension or invariant-metric premise.")),
                    Paragraph(Text("Injectivity of the two original projections forces ker(A) to be the real line through x, and the kernel of evaluation at x to be the real line through A. Both bijections identify the quotient spaces, so rank-nullity transfers equality of the two original dimensions. The invariant positive form is constructed by OriginalCompactActionMetric.compact_action_metric on this same compact G and full W; every original curve velocity is skew for that form. Commutation with A puts Kx in ker(A), skewness makes that multiple orthogonal to x, and definiteness forces it to zero. Evaluation's kernel then gives the centralizer line through A.")),
                    Paragraph(Text("On the actual tangent Lie algebra the proof constructs kappa(K,L)=-one-half times the real trace on W of KL. An orthonormal basis for the derived positive form expresses minus trace(K squared) as a sum of squared norms of K applied to basis vectors, strictly positive for every nonzero faithful operator. Cyclic trace proves symmetry and adjoint invariance. The proof actually applies RankOneInvariantMetric.finrank_eq_one_or_three with this constructed metric and the derived centralizer line. Equality of the original dimensions and Ax=0 exclude dimension one: in that case x spans all of W, making A the zero actual operator. Both dimensions are therefore three.")),
                    Paragraph(Text("This is a source-faithful dependency of OMEGAQ-008 Theorem 5.1, Sections 2 through 5, on its actual original matrix action. The curve-exponential equivalence in this document supplies the comparison with the all-real matrix exponential-membership convention. The reverse full-relation implication is constructed below from the full skew range. A separately supplied manifold GroupLieAlgebra identification, equality of the identity component with SO, the SO/O group alternatives, and the probability frontend require their respective further constructions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-skew-exponentials-in-component"),
                DeclarationHandle.Create(Prefix + "original_exponential_rigidity"), H("Original skew exponentials lie in the original component"),
                StatementSource.FromAuthor(RigidityFormula(true)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the original compactness and full-relation witness assumptions, the same derived positive form B is invariant under G, both original dimensions are three, and the original inclusion fills all B-skew endomorphisms. Every element in the actual identity connected component has determinant one. For every continuous endomorphism K whose underlying linear map is B-skew and every real t, an actual element of that component has value exp(t K).")),
                    Paragraph(Text("The actual curve-exponential equivalence first puts each exponential unit in G. The unit is packaged from Mathlib's isUnit_exp. Its value is exp(t K) and its inverse value is exp(-t K); continuity of both coordinates proves continuity in the actual units topology. The resulting G-valued curve passes through one. Its connected image lies in the connected component of one. The original full-skew range equality supplies membership of each requested K in the actual velocity subspace.")),
                    Paragraph(Text("The determinant restriction uses an orthonormal basis for B to identify each original group element with an actual orthogonal matrix, hence its determinant has square one. The determinant is continuous in the original operator topology. On the connected component of one the sign is constant, and the identity fixes it to one. Thus this actual component is contained in SO(W,B), while it contains all skew exponentials. Identifying all of SO(W,B) with those exponentials or their products, the opposite component inclusion, and G=SO or O remain separate mathematical obligations. The theorem does not assume those conclusions and does not substitute the ambient orthogonal group for the original G."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reverse-entire-original-relation"),
                DeclarationHandle.Create(Prefix + "fullReciprocity_of_full_skew"), H("The full reverse Q8 implication"),
                StatementSource.FromAuthor(ReverseFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the same original matrix subgroup G and its actual curve Lie algebra on the full W, assume W has dimension three and the range of the original inclusion equals all skew endomorphisms for a positive form B. Then there exist nonzero A in that actual Lie algebra and nonzero x in the same W with Ax=0 and both canonical projections of fullRelation G A x bijective. This is the reverse implication of the algebraic rigidity characterization. Compactness is not required again in this direction, since the hypotheses already identify the entire actual velocity range.")),
                    Paragraph(Text("A B-orthonormal frame constructs the actual plane rotation T with T(b0)=b1, T(b1)=-b0, and T(b2)=0. Set x=b2 and obtain A from the full original range. The proof establishes ker(A)=R x and range(A)=x-perp. Every original velocity is B-skew, so evaluation at x has image in x-perp. For every y perpendicular to x the rank-two skew map v maps to B(x,v)y-B(y,v)x takes x to y; the full original range supplies its actual velocity. Thus the evaluation image is exactly the same x-perp. Faithfulness bounds the actual Lie algebra dimension by three, and rank-nullity then forces its evaluation kernel to be exactly R A.")),
                    Paragraph(Text("Both projection proofs use every pair in the image of the full kernel Kx+Ay=0. For each projection, its zero fiber is trivial by the opposite kernel line. For either requested quotient class, the common image supplies a solution on the other side. These are separate injectivity and surjectivity arguments for the actual two canonical projections. No graph branch is chosen and no smaller representation or source orbit replaces W. This implication does not identify the full original group with SO or O and does not establish the operational probability frontend."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-full-skew-algebra"),
                DeclarationHandle.Create(Prefix + "original_rigidity"), H("The original action fills the orthogonal Lie algebra"),
                StatementSource.FromAuthor(RigidityFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under exactly the same compactness, nonzero-witness, annihilation and entire-relation hypotheses, there exists a positive form B invariant under the original G such that both original dimensions are three and the range of the actual inclusion of its curve Lie algebra into End(W) equals all B-skew endomorphisms of that same W. The inclusion is the original matrix action. Neither a supplied representation isomorphism nor a separately assumed dimension or centralizer is used.")),
                    Paragraph(Text("The dimension theorem supplies the three-dimensional faithful range. For a positive form on a three-dimensional space, the three off-diagonal coefficients in an orthonormal basis determine a skew endomorphism: the diagonal coefficients vanish and skewness determines the remaining coefficients. This embeds the full skew subspace into three real coordinates, giving its dimension at most three. Every actual curve velocity is B-skew, so the faithful three-dimensional range is a subspace of that skew subspace with the same dimension and therefore equals it."))), DescribeRole.Theorem))));

    private static Formula ReverseFormula()
    {
        Formula w = F.Id("W"), g = F.Id("G"), b = F.Id("B"), a = F.Id("A"), x = F.Id("x");
        return Disp(Seq(Forall, Sp, w, Comma, g, Comma, b, Comma, Esc,
            Call("FiniteDimensionalRealInnerProductSpace",w), Sp, Land, Sp,
            Call("SubgroupOfUnitsEnd",g,w), Sp, Land, Sp,
            Call("InnerProductSpaceCore",F.Id("R"),w,b), Sp, Land, Sp,
            Call("finrank",F.Id("R"),w), Eq, D(3), Sp, Land, Sp,
            Call("range",Call("originalAction",g)), Eq, Call("skewEndomorphisms",b),
            Sp, Rightarrow, Sp, Exists, Sp, a, Colon, Call("Lie",g), Comma, Esc,
            Exists, Sp, x, Colon, w, Comma, Esc,
            a, Neq, D(0), Sp, Land, Sp, x, Neq, D(0), Sp, Land, Sp,
            Call("A",x), Eq, D(0), Sp, Land, Sp, Call("FullReciprocity",g,a,x)));
    }

    private static Formula ExponentialFormula()
    {
        Formula w = F.Id("W"), g = F.Id("G"), k = F.Id("K"), t = F.Id("t"), u = F.Id("u");
        return Disp(Seq(Forall, Sp, w, Comma, g, Comma, Esc,
            Call("FiniteDimensionalRealInnerProductSpace",w), Sp, Land, Sp,
            Call("SubgroupOfUnitsEnd",g,w), Sp, Land, Sp, Call("IsCompact",g), Sp, Rightarrow, Sp,
            Forall, Sp, k, Colon, Call("ContinuousEnd",F.Id("R"),w), Comma, Esc,
            Open, Call("Member",k,Call("velocitySpace",g)), Close, Sp, Iff, Sp,
            Open, Forall, Sp, t, Colon, F.Id("R"), Comma, Esc,
            Exists, Sp, u, Colon, Call("UnitsContinuousEnd",F.Id("R"),w), Comma, Esc,
            Call("Member",u,g), Sp, Land, Sp,
            Call("value",u), Eq, Call("exp",Seq(t,Cdot,Sp,k)), Close));
    }

    private static Formula CurveFormula()
    {
        Formula w = F.Id("W"), g = F.Id("G"), k = F.Id("K"), c = F.Id("c");
        return Disp(Seq(Forall, Sp, w, Comma, g, Comma, Esc,
            Call("FiniteDimensionalRealInnerProductSpace",w), Sp, Land, Sp,
            Call("SubgroupOfUnitsEnd",g,w), Sp, Rightarrow, Sp,
            Forall, Sp, k, Colon, Call("ContinuousEnd",F.Id("R"),w), Comma, Esc,
            Call("Member",k,Call("Carrier",Call("curveLieAlgebra",g))), Sp, Iff, Sp,
            Exists, Sp, c, Colon, F.Id("R"), Sp, To, Sp, g, Comma, Esc,
            Call("c",D(0)), Eq, D(1), Sp, Land, Sp,
            Call("HasDerivAt",Call("originalOperatorCurve",c),k,D(0))));
    }

    private static Formula RelationFormula()
    {
        Formula w = F.Id("W"), g = F.Id("G"), a = F.Id("A"), x = F.Id("x");
        return Disp(Seq(Forall, Sp, w, Comma, g, Comma, Esc,
            Call("FiniteDimensionalRealInnerProductSpace",w), Sp, Land, Sp,
            Call("SubgroupOfUnitsEnd",g,w), Sp, Rightarrow, Sp,
            Forall, Sp, a, Colon, Call("Lie",g), Comma, Esc,
            Forall, Sp, x, Colon, w, Comma, Esc,
            Call("fullRelation",g,a,x), Eq,
            Call("Image",Call("quotientPair",g,a,x),
                Call("Ker",Call("evaluationPlusAction",g,a,x)))));
    }

    private static Formula RigidityFormula(bool includeExponentials = false)
    {
        Formula w = F.Id("W"), g = F.Id("G"), a = F.Id("A"), x = F.Id("x"), b = F.Id("B");
        Formula dim(Formula v) => Call("finrank",F.Id("R"),v);
        return Disp(Seq(Forall, Sp, w, Comma, g, Comma, Esc,
            Call("FiniteDimensionalRealInnerProductSpace",w), Sp, Land, Sp,
            Call("SubgroupOfUnitsEnd",g,w), Sp, Land, Sp, Call("IsCompact",g), Sp, Rightarrow, Sp,
            Forall, Sp, a, Colon, Call("Lie",g), Comma, Esc, Forall, Sp, x, Colon, w, Comma, Esc,
            a, Neq, D(0), Sp, Land, Sp, x, Neq, D(0), Sp, Land, Sp, Call("A",x), Eq, D(0),
            Sp, Land, Sp, Call("FullReciprocity",g,a,x), Sp, Rightarrow, Sp,
            Exists, Sp, b, Colon, Call("InnerProductSpaceCore",F.Id("R"),w), Comma, Esc,
            Open, Forall, Sp, F.Id("h"), Colon, g, Comma, Esc,
            Forall, Sp, F.Id("u"), Comma, F.Id("v"), Colon, w, Comma, Esc,
            Call("B",Call("h",F.Id("u")),Call("h",F.Id("v"))), Eq,
            Call("B",F.Id("u"),F.Id("v")), Close, Sp, Land, Sp,
            dim(w), Eq, D(3), Sp, Land, Sp, dim(Call("Lie",g)), Eq, D(3), Sp, Land, Sp,
            Call("range",Call("originalAction",g)), Eq, Call("skewEndomorphisms",b),
            includeExponentials ? Seq(Sp, Land, Sp,
                Open, Forall, Sp, F.Id("h"), Colon, g, Comma, Esc,
                Call("Member",F.Id("h"),Call("connectedComponent",D(1),g)),
                Sp, Rightarrow, Sp, Call("det",Call("originalValue",F.Id("h"))), Eq, D(1), Close,
                Sp, Land, Sp, Forall, Sp, F.Id("K"), Colon, Call("ContinuousEnd",F.Id("R"),w), Comma, Esc,
                Call("Member",Call("underlyingLinearMap",F.Id("K")),Call("skewEndomorphisms",b)),
                Sp, Rightarrow, Sp, Forall, Sp, F.Id("t"), Colon, F.Id("R"), Comma, Esc,
                Exists, Sp, F.Id("h"), Colon, g, Comma, Esc,
                Call("Member",F.Id("h"),Call("connectedComponent",D(1),g)), Sp, Land, Sp,
                Call("originalValue",F.Id("h")), Eq, Call("exp",Seq(F.Id("t"),Cdot,Sp,F.Id("K"))))
                : Seq()));
    }

    private static Formula DimensionFormula()
    {
        Formula w = F.Id("W"), g = F.Id("G"), a = F.Id("A"), x = F.Id("x");
        Formula dim(Formula v) => Call("finrank",F.Id("R"),v);
        return Disp(Seq(Forall, Sp, w, Comma, g, Comma, Esc,
            Call("FiniteDimensionalRealInnerProductSpace",w), Sp, Land, Sp,
            Call("SubgroupOfUnitsEnd",g,w), Sp, Land, Sp, Call("IsCompact",g), Sp, Rightarrow, Sp,
            Forall, Sp, a, Colon, Call("Lie",g), Comma, Esc, Forall, Sp, x, Colon, w, Comma, Esc,
            a, Neq, D(0), Sp, Land, Sp, x, Neq, D(0), Sp, Land, Sp, Call("A",x), Eq, D(0),
            Sp, Land, Sp, Call("FullReciprocity",g,a,x), Sp, Rightarrow, Sp,
            dim(w), Eq, D(3), Sp, Land, Sp, dim(Call("Lie",g)), Eq, D(3)));
    }
}
