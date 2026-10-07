using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.State;

internal sealed class PaddedLawSetupRW2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetupRW2.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric matrix state invariants and padded driving laws.",
        H("Padded Law Setup RW2"),
        Blocks(
            Paragraph(Text("Symmetric matrix state invariants and padded driving laws. The results below relate padded law setup rw2 to the stochastic ellipsoid construction.")),
            Node("claim-1", "RawDataR", "Raw Data R",
                "PaddedLawSetup.RawData at the reach window. Identical field for field except window_lt_p, supp_radius and hwin, which are stated at WindowR2.windowR2 α n.", DescribeRole.Definition),
            Node("claim-2", "rawDataR_mono", "raw Data R mono",
                "RawDataR restricts, exactly as LatticeData.rawData_mono does for RawData: every field is either ∀ y ∈ W or independent of W.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
