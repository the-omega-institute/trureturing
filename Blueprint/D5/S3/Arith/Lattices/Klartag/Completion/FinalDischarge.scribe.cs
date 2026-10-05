using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Completion;

internal sealed class FinalDischargeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Completion/FinalDischarge.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform constants and completion of lattice packing.",
        H("Final Discharge"),
        Blocks(
            Paragraph(Text("Uniform constants and completion of lattice packing. The results below relate final discharge to the stochastic ellipsoid construction.")),
            Node("claim-1", "hq_win", "hq win",
                "Within the enlarged radial window, the quadratic constraint vectors have pairwise nonnegative inner products.", DescribeRole.Theorem),
            Node("claim-2", "hne_win", "hne win",
                "Every quadratic constraint vector indexed by the enlarged radial window is nonzero.", DescribeRole.Theorem),
            Node("claim-3", "kSet_A0C_win", "k Set A0C win",
                "The scalar initial quadratic form satisfies every constraint in the enlarged radial window.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
