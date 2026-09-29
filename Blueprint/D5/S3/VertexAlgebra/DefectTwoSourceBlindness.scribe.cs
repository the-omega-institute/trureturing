using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class DefectTwoSourceBlindnessDocument : IScribeDocumentDefinition
{
    private static Formula Plane(Formula a, Formula b) =>
        Call("plane", F.Id("g"), F.Id("h"), a, b);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two defect directions have zero cubic carry response on their entire span.",
        H("Two-source determinant blindness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-source-carry-blindness"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/DefectTwoSourceBlindness.two_source_carry_blind"),
                H("Two sources cannot detect the cubic carry"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("m"), Comma, Sp, F.Id("g"), Comma, Sp,
                    F.Id("h"), InMacro, Sp, F.Id("E"), Comma, Sp,
                    F.Id("a"), Comma, Sp, F.Id("b"), Comma, Sp,
                    F.Id("c"), Comma, Sp, F.Id("d"), Comma, Sp,
                    F.Id("e"), Comma, Sp, F.Id("f"), InMacro, Sp,
                    F.Id("F"), Underscore, D(2), Comma, Esc,
                    Call("dot", Call("carry", Call("ell", F.Id("m")),
                        Plane(F.Id("a"), F.Id("b")), Plane(F.Id("c"), F.Id("d"))),
                        Plane(F.Id("e"), F.Id("f"))), Eq, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every plane expression is a linear combination "
                    + "of the same two defect labels g and h. The carry of two such "
                    + "expressions is their wedge product, and pairing it with any "
                    + "third expression from that plane is zero. Thus arbitrary binary "
                    + "composition of labels from two fixed sources remains unable to "
                    + "produce a negative cubic determinant sign. An independent third "
                    + "label is required to observe it."))),
                DescribeRole.Theorem))));
}
