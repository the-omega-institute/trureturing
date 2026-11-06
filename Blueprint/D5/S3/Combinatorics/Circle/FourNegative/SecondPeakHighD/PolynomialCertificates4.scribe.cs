using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD;
internal sealed class PolynomialCertificates4Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive coefficient cone certificates 4", H("Positive coefficient cone certificates 4"),
        Blocks(
            Paragraph(Text("Each displayed endpoint slack is expanded after shifting the declared cone to nonnegative coordinates. Ring verifies the exact rational polynomial identity and positivity verifies every resulting term. The inequalities are universal over the original rational cone and feed the integer adapter used by the small-a selector; numerical sampling is not used.")),
            Describe.Lean(DescribeId.Create("highd-polynomialcertificates4-tail-r16"), DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/PolynomialCertificates4.tail_R16"), H("tail_R16"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Consumed in the construction described here, with the exact telescope supplied by Lean."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("highd-polynomialcertificates4-tail-r16q4"), DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/PolynomialCertificates4.tail_R16q4"), H("tail_R16q4"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Consumed in the construction described here, with the exact telescope supplied by Lean."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("highd-polynomialcertificates4-tail-r16odd"), DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/PolynomialCertificates4.tail_R16odd"), H("tail_R16odd"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Consumed in the construction described here, with the exact telescope supplied by Lean."))), DescribeRole.Theorem)), []));
}
