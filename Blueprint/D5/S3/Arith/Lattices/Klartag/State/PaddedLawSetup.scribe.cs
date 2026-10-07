using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.State;

internal sealed class PaddedLawSetupDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetup.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric matrix state invariants and padded driving laws.",
        H("Padded Law Setup"),
        Blocks(
            Paragraph(Text("Symmetric matrix state invariants and padded driving laws. The results below relate padded law setup to the stochastic ellipsoid construction.")),
            Node("claim-1", "stdGaussian_prodL2", "std Gaussian prod L2",
                "The value-type fact. The standard Gaussian on the L² product *is* the product of the two standard Gaussians — so adjoining the fresh coordinate to the value type is exactly adjoining an independent N(0,1), with no second factor and no reshuffling.", DescribeRole.Theorem),
            Node("claim-2", "TailSideHyp", "Tail Side Hyp",
                "The one probabilistic input of chainRaw2_of_walk, on chainSetup.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
