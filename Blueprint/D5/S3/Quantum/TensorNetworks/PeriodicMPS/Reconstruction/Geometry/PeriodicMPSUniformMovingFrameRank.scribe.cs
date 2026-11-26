using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformMovingFrameRankDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameRank";
    private const string Title = "Noncoordinate prime exclusion from native criticality";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformmovingframerank"),
                DeclarationHandle.Create(Module + ".no_noncoordinate_prime_of_genericNativeCriticalMatrix"),
                H("Generic native matrices exclude vertical divisors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For m at least three, an irreducible root divisor avoiding the trace sum and all four root coordinates cannot give native criticality on every admissible generic paired section."))),
                DescribeRole.Theorem))));
}
