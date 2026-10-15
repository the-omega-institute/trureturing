using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockLiteralLeadingCoefficientDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockLiteralLeadingCoefficient.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "First nonzero scalar coefficient of the original square-root chart", H("Literal Leading Coefficient"), Blocks(
            Describe.Lean(DescribeId.Create("literal-clearing-leading-coefficient"),
                DeclarationHandle.Create(Prefix + "literal_clearing_leading_coefficient"), H("Signed first coefficient"),
                StatementSource.FromAuthor(Disp(Call("LiteralClearingLeading", F.Id("g"), F.Id("s")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("For all signed integers g and s, the original finite clearing polynomial paired with choose((s-d)/2,2g.toNat) gives 2^(-2g). Substitution of the genuine inverse square-root series factors off exactly X^(2g.toNat). This is the half exponent, not the auxiliary exponent-E binomial chart. The coefficient is independent of s; neither higher coefficients nor all-order iterates are asserted."))), DescribeRole.Theorem))));
}
