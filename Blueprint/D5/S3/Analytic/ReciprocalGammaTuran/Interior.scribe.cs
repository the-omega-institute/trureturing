using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ReciprocalGammaTuran;

internal sealed class InteriorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Negative reciprocal Gamma Turanian coefficients.",
        H("Interior coefficients"), Blocks(
            Describe.Lean(DescribeId.Create("reciprocal-gamma-second-coefficient-continuous"),
                DeclarationHandle.Create("D5/S3/Analytic/ReciprocalGammaTuran/Interior.continuous_turanCoeff_two"),
                H("Continuity in all parameters"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The second coefficient for the constant unit sequence is jointly continuous in mu, alpha and beta on the whole real parameter space. The inverse complex Gamma function is entire. Restriction to the real axis gives continuity even at its zeros, and finite sums and products preserve continuity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reciprocal-gamma-interior-negative-coefficient"),
                DeclarationHandle.Create("D5/S3/Analytic/ReciprocalGammaTuran/Interior.interior_failure"),
                H("Strictly interior violations"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There exist positive alpha and beta and mu at least minus one such that mu+alpha and mu+beta are strictly positive and the second coefficient is strictly negative. Continuity preserves the boundary negativity when mu is increased by a sufficiently small positive amount."))), DescribeRole.Theorem))));
}
