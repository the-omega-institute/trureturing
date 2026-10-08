using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Tail;

internal sealed class TailSideSetup2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup2.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lattice tail bounds along the matrix walk.",
        H("Tail Side Setup2"),
        Blocks(
            Paragraph(Text("Lattice tail bounds along the matrix walk. The results below relate tail side setup2 to the stochastic ellipsoid construction.")),
            Node("claim-1", "measurable_of_active_vec", "measurable of active vec",
                "ChainWiring.measurable_of_active, vector-valued. A statistic of the active set alone is measurable; the proof is the same finite partition over W.powerset.", DescribeRole.Theorem),
            Node("claim-2", "extendc", "extendc",
                "A truncated past, read back as a full path at scale c.", DescribeRole.Definition),
            Node("claim-5", "dirOf", "dir Of",
                "The chain's projected direction at q y, normalised.", DescribeRole.Definition),
            Node("claim-10", "NormData", "Norm Data",
                "The two identities RawData does not carry: Klartag's eq. (61) at time zero. Both are immediate for the chain's own q y = ChainWiring.qUT (α • toE n y) and A₀ = a0C n • Id.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
