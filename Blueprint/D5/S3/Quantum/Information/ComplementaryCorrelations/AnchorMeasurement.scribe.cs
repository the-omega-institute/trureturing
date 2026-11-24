using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.ComplementaryCorrelations;

internal sealed class AnchorMeasurementDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/qian2026complementarycorrelations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The product-anchor quadratic.",
        H("The product-anchor quadratic"),
        Blocks(
            Paragraph(Text("Definition 7.2 and equation (39) of Qian use a quadratic form at a faithful product state. The quantum term is the actual Kubo–Mori trace pairing of the tangent with the derivative of the logarithm.")),
            Describe.Lean(DescribeId.Create("qian-anchormeasurement-marginalfree"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurement.MarginalFree"),
                H("Fixed-marginal directions"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo([Source]),
                Blocks(Paragraph(Text("The joint tangent is Hermitian and both partial traces vanish."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qian-anchormeasurement-measurementfisher"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurement.measurementFisher"),
                H("Fisher form of the measured distribution"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo([Source]),
                Blocks(Paragraph(Text("The diagonal entries of the tangent and state in the product basis give the outcome derivatives and probabilities. The form sums the squares of the derivatives divided by those probabilities."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qian-anchormeasurement-anchorquadraticin"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurement.anchorQuadraticIn"),
                H("The term in equation (39)"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo([Source]),
                Blocks(Paragraph(Text("At the product state the trace pairing of the tangent with its log resolvent derivative is reduced by the two measured Fisher forms."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qian-anchormeasurement-acc23allbases"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurement.ACC₂₃AllBases"),
                H("Anchor convexity for qubit–qutrit pairs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo([Source]),
                Blocks(Paragraph(Text("The inequality ranges over faithful marginal states, all fixed-marginal directions, and all pairs of local unitary bases with squared overlaps one half on Alice and one third on Bob."))), DescribeRole.Definition))));
}
