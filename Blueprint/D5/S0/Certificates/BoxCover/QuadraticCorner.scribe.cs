using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.BoxCover;

internal sealed class QuadraticCornerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rational enclosures of recursive quadratic polynomials.",
        H("QuadraticCorner"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quadraticcorner-poly"),
                DeclarationHandle.Create("D5/S0/Certificates/BoxCover/QuadraticCorner.Poly"),
                H("Recursive quadratic syntax"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each coordinate is eliminated at both closed endpoints. The lower correction is max(d,0) times the squared interval width divided by four; the upper correction uses max(-d,0). Induction encloses every real point of the box, including zero-width intervals."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadraticcorner-lower"),
                DeclarationHandle.Create("D5/S0/Certificates/BoxCover/QuadraticCorner.lower"),
                H("Exact lower enclosure"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each coordinate is eliminated at both closed endpoints. The lower correction is max(d,0) times the squared interval width divided by four; the upper correction uses max(-d,0). Induction encloses every real point of the box, including zero-width intervals."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadraticcorner-upper"),
                DeclarationHandle.Create("D5/S0/Certificates/BoxCover/QuadraticCorner.upper"),
                H("Exact upper enclosure"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each coordinate is eliminated at both closed endpoints. The lower correction is max(d,0) times the squared interval width divided by four; the upper correction uses max(-d,0). Induction encloses every real point of the box, including zero-width intervals."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadraticcorner-encloses"),
                DeclarationHandle.Create("D5/S0/Certificates/BoxCover/QuadraticCorner.encloses"),
                H("Real point enclosure with diagonal correction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each coordinate is eliminated at both closed endpoints. The lower correction is max(d,0) times the squared interval width divided by four; the upper correction uses max(-d,0). Induction encloses every real point of the box, including zero-width intervals."))), DescribeRole.Theorem))));
}
