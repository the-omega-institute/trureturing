using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Cone;

internal sealed class SourceConeAdmissibilityDocument : IScribeDocumentDefinition
{
    private const string P = "D5/S3/FluidDynamics/Cone/SourceConeAdmissibility.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compact source data satisfy eventual positive definiteness of the cone matrix.",
        H("Source cone admissibility"), Blocks(
            Describe.Lean(DescribeId.Create("source-cone-equation-gap"), DeclarationHandle.Create(P + "compact_equation_eleven_gap"), H("Equation eleven gap"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The strict source criterion yields uniform relaxed cone inequalities above one amplitude threshold."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("source-cone-matrix-positive"), DeclarationHandle.Create(P + "compact_source_coneMatrix_posDef"), H("Source derived matrix positivity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For compact continuous source data and an explicit lower bound on the matrix parameter, all sufficiently large amplitudes give positive definite cone matrices."))), DescribeRole.Theorem))));
}
