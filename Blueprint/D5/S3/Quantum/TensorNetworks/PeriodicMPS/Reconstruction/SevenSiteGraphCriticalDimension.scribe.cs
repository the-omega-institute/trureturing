using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSiteGraphCriticalDimensionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteGraphCriticalDimension";
    private const string Title = "The compact seven-site exceptional set has dimension at most six";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(Describe.Lean(DescribeId.Create("sevensitegraphcriticaldimension-result"),
            DeclarationHandle.Create(Module + ".dimH_graphBadLocus_le"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The union of the ordinary chart boundary and the closure of the ordinary rank-deficient locus in the compact seven-site trace graph is compact and has real Hausdorff dimension at most six.")),
                Paragraph(Text("In the ordinary coordinates, the zero mixed coordinate has a six-real-dimensional parametrization. Away from that set, rank failure forces every tested minor to vanish on the aligned physical slice. The differentiable cover of the critical slice and its phase charts yields the same dimension bound for this part."))),
            DescribeRole.Theorem))));
}
