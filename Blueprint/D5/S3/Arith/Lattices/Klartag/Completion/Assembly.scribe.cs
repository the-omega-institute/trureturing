using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Completion;

internal sealed class AssemblyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Completion/Assembly.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform constants and completion of lattice packing.",
        H("Assembly"),
        Blocks(
            Paragraph(Text("Uniform constants and completion of lattice packing. The results below relate assembly to the stochastic ellipsoid construction.")),
            Node("claim-1", "sqrt_det_le", "sqrt det le",
                "Klartag eq. (68), with the constant written out. log det A ≤ C' − 4 log n gives Vol(E_A) ≥ e^{−C'/2}·n²·Vol(Bᴺ). With C' the universal constant of Lemma 5.2 this is c₀ = e^{−C'/2}: the n² of the theorem statement, produced here and nowhere else.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
