using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Completion;

internal sealed class Theorem2R4Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Completion/Theorem2R4.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform constants and completion of lattice packing.",
        H("Theorem2R4"),
        Blocks(
            Paragraph(Text("Uniform constants and completion of lattice packing. The results below relate theorem2r4 to the stochastic ellipsoid construction.")),
            Node("claim-1", "wComb", "w Comb",
                "The combined profileAt weight. No chain, no g, no record: a function of (A, B, α, m) alone. This is the weight the light-contact hypothesis is stated at.", DescribeRole.Definition),
            Node("claim-2", "QOf", "QOf",
                "The canonical ChainRaw3 at the adopted data: the reach-2 chain record, weights swapped.", DescribeRole.Definition),
            Node("claim-4", "c3clamp", "c3clamp",
                "c3Adopted'' clamped below the threshold, so the unrestricted admissibility facts hold.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
