using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Construction;

internal sealed class LatticeDataRDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Construction/LatticeDataR.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construction A lattices, covolumes and ellipsoid transfer.",
        H("Lattice Data R"),
        Blocks(
            Paragraph(Text("Construction A lattices, covolumes and ellipsoid transfer. The results below relate lattice data r to the stochastic ellipsoid construction.")),
            Node("claim-2", "tailSideHyp_filterR", "tail Side Hyp filter R",
                "TailSideHyp on a restricted window, given a producer at the full window. The producer is a hypothesis because TailSideSetup2.tailSideHyp_of_rawData demands a windowC-shaped RawData; everything else is LatticeData.tailSideHyp_filter's content.", DescribeRole.Theorem),
            Node("claim-3", "mem_shellR_of_shell", "mem shell R of shell",
                "Coverage at the reach window, with the outer radius written additively.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
