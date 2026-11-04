using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class OriginalCompactReciprocityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/OriginalCompactReciprocity.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The entire original first-order relation forces dimension three on the same compact matrix action.",
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
            Describe.Lean(DescribeId.Create("original-dimension-three"),
                DeclarationHandle.Create(Prefix + "finrank_eq_three"), H("Both original dimensions are three"),
                StatementSource.FromAuthor(DimensionFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume only that the original subgroup is compact and that A and x are nonzero, Ax=0, and FullReciprocity holds. Then the real dimensions of the original W and its actual curve Lie algebra are both three. Nontriviality of W follows from the nonzero witness; all finite dimensions remain in the quantified domain. There is no irreducibility, transitivity, centralizer, rank, dimension or invariant-metric premise.")),
                    Paragraph(Text("Injectivity of the two original projections forces ker(A) to be the real line through x, and the kernel of evaluation at x to be the real line through A. Both bijections identify the quotient spaces, so rank-nullity transfers equality of the two original dimensions. The invariant positive form is constructed by OriginalCompactActionMetric.compact_action_metric on this same compact G and full W; every original curve velocity is skew for that form. Commutation with A puts Kx in ker(A), skewness makes that multiple orthogonal to x, and definiteness forces it to zero. Evaluation's kernel then gives the centralizer line through A.")),
                    Paragraph(Text("On the actual tangent Lie algebra the proof constructs kappa(K,L)=-one-half times the real trace on W of KL. An orthonormal basis for the derived positive form expresses minus trace(K squared) as a sum of squared norms of K applied to basis vectors, strictly positive for every nonzero faithful operator. Cyclic trace proves symmetry and adjoint invariance. The proof actually applies RankOneInvariantMetric.finrank_eq_one_or_three with this constructed metric and the derived centralizer line. Equality of the original dimensions and Ax=0 exclude dimension one: in that case x spans all of W, making A the zero actual operator. Both dimensions are therefore three.")),
                    Paragraph(Text("This is a source-faithful dependency of OMEGAQ-008 Theorem 5.1, Sections 2 through 5, on its actual original matrix action. A formal comparison of the direct curve construction with separately supplied manifold GroupLieAlgebra or exponential-membership conventions is not supplied. Integration to the actual identity component SO, the SO/O group alternatives, the reverse full-relation implication, and the probability frontend remain outside these algebraic theorems."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-full-skew-algebra"),
                DeclarationHandle.Create(Prefix + "original_rigidity"), H("The original action fills the orthogonal Lie algebra"),
                StatementSource.FromAuthor(RigidityFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under exactly the same compactness, nonzero-witness, annihilation and entire-relation hypotheses, there exists a positive form B invariant under the original G such that both original dimensions are three and the range of the actual inclusion of its curve Lie algebra into End(W) equals all B-skew endomorphisms of that same W. The inclusion is the original matrix action. Neither a supplied representation isomorphism nor a separately assumed dimension or centralizer is used.")),
                    Paragraph(Text("The dimension theorem supplies the three-dimensional faithful range. For a positive form on a three-dimensional space, the three off-diagonal coefficients in an orthonormal basis determine a skew endomorphism: the diagonal coefficients vanish and skewness determines the remaining coefficients. This embeds the full skew subspace into three real coordinates, giving its dimension at most three. Every actual curve velocity is B-skew, so the faithful three-dimensional range is a subspace of that skew subspace with the same dimension and therefore equals it."))), DescribeRole.Theorem))));

    private static Formula CurveFormula() => Disp(Seq(
        Call("Lie",F.Id("G")), Eq, OpenBrace, F.Id("K"), Colon, Esc,
        Exists, Sp, F.Id("c"), Colon, F.Id("R"), Sp, To, Sp, F.Id("G"), Comma, Esc,
        Call("c",D(0)), Eq, D(1), Sp, Land, Sp,
        Call("HasDerivAt",Call("originalOperatorCurve",F.Id("c")),F.Id("K"),D(0)), CloseBrace));

    private static Formula RelationFormula() => Disp(Seq(
        Call("T",F.Id("A"),F.Id("x")), Eq,
        Call("Image",F.Id("quotientPair"),Call("Ker",F.Id("evaluationPlusAction")))));

    private static Formula RigidityFormula()
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
            Call("range",Call("originalAction",g)), Eq, Call("skewEndomorphisms",b)));
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
