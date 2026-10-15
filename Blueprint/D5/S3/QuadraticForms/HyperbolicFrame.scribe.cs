using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class HyperbolicFrameDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A supplied literal hyperbolic pair extends to a frame with both matrix inverses and both all-row duality equations.",
        H("Literal Hyperbolic Frames"),
        Blocks(Describe.Lean(
            DescribeId.Create("literal-hyperbolic-frame"),
            DeclarationHandle.Create("D5/S3/QuadraticForms/HyperbolicFrame.exists_frame_with_literal_duals"),
            H("Orthogonal-complement frame construction"),
            StatementSource.FromAuthor(Disp(Seq(
                Forall, Sp, F.Id("K"), Comma, Sp, F.Id("d"), Comma, Sp,
                F.Id("B"), Comma, Sp, F.Id("n"), Comma, Sp, F.Id("m"), Comma, Sp,
                Call("Field", F.Id("K")), Sp, Land, Sp, Call("IsSymm", F.Id("B")), Sp, Land, Sp,
                Call("B", F.Id("n"), F.Id("n")), Sp, Eq, Sp, Num(0), Sp, Land, Sp,
                Call("B", F.Id("m"), F.Id("m")), Sp, Eq, Sp, Num(0), Sp, Land, Sp,
                Call("B", F.Id("m"), F.Id("n")), Sp, Eq, Sp, Num(1), Sp, Rightarrow, Sp,
                Exists, Sp, F.Id("F"), Comma, Sp, F.Id("I"), Comma, Sp,
                F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
                F.Id("I"), Times, F.Id("F"), Sp, Eq, Sp, Num(1), Sp, Land, Sp,
                F.Id("F"), Times, F.Id("I"), Sp, Eq, Sp, Num(1), Sp, Land, Sp,
                F.Id("x"), Sp, Neq, Sp, F.Id("y"), Sp, Land, Sp,
                Call("F", F.Id("x")), Sp, Eq, Sp, F.Id("n"), Sp, Land, Sp,
                Call("F", F.Id("y")), Sp, Eq, Sp, F.Id("m"), Sp, Land, Sp,
                Forall, Sp, F.Id("r"), Comma, Sp,
                Call("B", Call("F", F.Id("y")), Call("F", F.Id("r"))), Sp, Eq, Sp,
                Call("if", Seq(F.Id("r"), Eq, F.Id("x")), Num(1), Num(0)), Sp, Land, Sp,
                Forall, Sp, F.Id("r"), Comma, Sp,
                Call("B", Call("F", F.Id("x")), Call("F", F.Id("r"))), Sp, Eq, Sp,
                Call("if", Seq(F.Id("r"), Eq, F.Id("y")), Num(1), Num(0))))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For any field K and natural dimension d, let B be a symmetric bilinear form on vectors Fin d to K. Given literal vectors n and m with B(n,n)=B(m,m)=0 and B(m,n)=1, the theorem constructs square d by d matrices F and I and distinct axes x,y in Fin d. Both I times F and F times I equal the identity. The row F(x) is exactly n and F(y) is exactly m. For every frame row r, B(F(y),F(r)) is one at r=x and zero elsewhere, while B(F(x),F(r)) is one at r=y and zero elsewhere.")),
                Paragraph(Text("The unit cross-pairing proves that n is nonzero and that the two vectors are linearly independent. On their span, testing a radical vector against m and n kills its two coefficients. Mathlib then gives the complementary orthogonal subspace. Its finite basis and the plane basis are assembled through the existing product-basis and complementary-subspace linear equivalence, and reindexed to Fin d using the proved basis cardinality. The cross-pairings on every complement row vanish by orthogonality.")),
                Paragraph(Text("Rows are the transpose of the change-of-basis matrix from this new basis to the standard coordinate basis. The inverse is the transpose of the reverse change-of-basis matrix. Both matrix inverse equations follow from the respective compositions being the identity; neither equation is assumed or replaced by a determinant-only conclusion.")),
                Paragraph(Text("No global nondegeneracy, real signature or characteristic restriction is required for this conditional frame construction: the supplied hyperbolic plane itself has the needed nondegenerate restriction. This theorem does not assume existence of such a pair. Its actual original-Q application must first construct n from nonzero integral charge and the inverse complex Gram matrix, then use the literal existing adaptedPartner formula for m. Pair existence is supplied by the separate null-separation construction and adaptedPartner_relations, never by a record field.")),
                Paragraph(Text("The original termination convention is xDual equals pairing with the y row, and yDual equals pairing with the x row. Both equations hold for every row, including both special axes. The original physical consumers still require both inverse-Gram equations and critical rank twenty-six. These are complex bilinear frames, not Hermitian, real, positive or unitary frames. No no-ghost or physical completion follows solely from this construction."))),
            DescribeRole.Theorem))));
}
