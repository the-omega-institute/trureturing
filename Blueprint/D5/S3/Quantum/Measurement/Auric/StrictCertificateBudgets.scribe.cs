using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class StrictCertificateBudgetsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp spectral values of the strict certificates",
        H("Sharp spectral values of the strict certificates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("direct-certificate-maximum"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/StrictCertificateBudgets.direct_certificate_maximum"),
                H("Direct proportional columns in the original labels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("When the deficits fit, a positive normalized weight vector satisfying the prescribed row masses gives an attained direct spectral maximum. Sorting the weights reindexes the rows together with their missing-label columns. Their multiplicities and total score are preserved on returning to the original labels."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complement-certificate-maximum"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/StrictCertificateBudgets.complement_certificate_maximum"),
                H("Complementary clipped columns in the original labels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Positive weights and normalized clipped columns with the stated row masses give an attained complementary spectral maximum. The allowed column sum is strictly decreasing at the level one, so each certified scale is the canonical one. This makes the ordering argument valid for every certificate satisfying the original-label equations."))),
                DescribeRole.Theorem))));
}
