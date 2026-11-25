using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.ComplementaryCorrelations;

internal sealed class AnchorMeasurementBKMDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dual BKM estimate for measurement scores.",
        H("Dual BKM estimate for measurement scores"),
        Blocks(
            Describe.Lean(DescribeId.Create("qian-anchormeasurementbkm-omega-le-simpson"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurementBKM.omega_le_simpson"),
                H("Simpson bound for the inverse BKM form"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In an eigenbasis of the faithful state, each pair of eigenvalues contributes a logarithmic mean. The Simpson bound controls that mean by the arithmetic and geometric mean contributions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("qian-anchormeasurementbkm-anchorquadraticin-nonneg-of-simpson"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurementBKM.anchorQuadraticIn_nonneg_of_simpson"),
                H("Dual estimate implies anchor convexity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Center the two local score functions in each measured distribution. The marginal-free condition identifies their trace pairings with the measured Fisher forms. Weighted Cauchy–Schwarz then reduces nonnegativity to a Simpson bound on the joint centered observable."))), DescribeRole.Theorem))));
}
