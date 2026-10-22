using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ReciprocalGammaTuran;

internal sealed class BoundaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Negative reciprocal Gamma Turanian coefficients.",
        H("Boundary coefficients"), Blocks(
            Describe.Lean(DescribeId.Create("reciprocal-gamma-half-coefficient"),
                DeclarationHandle.Create("D5/S3/Analytic/ReciprocalGammaTuran/Boundary.d_two_half"),
                H("The half-shift coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At mu=-1/2 and alpha=beta=1/2, the second coefficient equals 1-10/(3 pi). Euler reflection at the half shift and Gamma recurrence evaluate all six reciprocal Gamma factors."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reciprocal-gamma-half-coefficient-negative"),
                DeclarationHandle.Create("D5/S3/Analytic/ReciprocalGammaTuran/Boundary.d_two_half_neg"),
                H("A negative boundary coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact half-shift coefficient is strictly negative because pi is less than 3.15, which is less than 10/3."))), DescribeRole.Theorem))));
}
