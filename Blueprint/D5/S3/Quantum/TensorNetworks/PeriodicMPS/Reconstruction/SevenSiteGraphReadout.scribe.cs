using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSiteGraphReadoutDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteGraphReadout";
    private const string Title = "Descent of singleton marginal fibers from the trace graph";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(Describe.Lean(DescribeId.Create("sevensitegraphreadout-result"),
            DeclarationHandle.Create(Module + ".state_singletons_of_graph_singletons"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("If a relatively open dense subset of the compact seven-site trace graph consists of singleton fibers of the Pauli observation, the compact state source has a relatively open dense subset of singleton fibers of the adjacent two-site marginal.")),
                Paragraph(Text("The state projection forgets the weighted trace projector and is continuous and surjective. Equality of marginals agrees with equality of the graph readings. The singleton-fiber locus contains every lift of each state in its image, so openness descends through the quotient map."))),
            DescribeRole.Theorem))));
}
