using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class TwoQueryPhaseDiscriminationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/TwoQueryPhaseDiscrimination.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/sieniawski2026adaptivechannel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp trace-distance separation for two independent phase-dephasing queries.",
        H("Two-query longitudinal dephasing discrimination"),
        Blocks(
            Theorem("phase-discrimination-converse", "experiment_traceNorm_le",
                "An upper bound for strategies with finite retained memory",
                "A complementary mixture of two phase unitaries represents each hypothesis. At two queries the mixed-label terms cancel, even through an isometric control. Comparing the remaining pure paths through their common intermediate path gives the upper bound."),
            Theorem("phase-discrimination-attainment", "parallel_attains",
                "A parallel pure probe attains the bound",
                "A two-qubit input places equal weights on complementary basis strings. Choosing the total weight on the equal strings minimizes the overlap of the two extreme pure outputs. This saturates the trace-distance bound."))));

    private static DocumentBlock Theorem(string id, string name, string title, string prose) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Module + name),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))),
            DescribeRole.Theorem);
}
