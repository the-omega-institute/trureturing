using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class EulerPentagonalTrisectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/EulerPentagonalTrisection.";
    private static readonly LibraryNoteRef Question = LibraryNoteRef.Create("D5/L/Fourier/bringmann2024periodic");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete pentagonal reindexing into the three weighted Jacobi sections.", H("EulerPentagonalTrisection"), Blocks(
            Paragraph(Text("The map from Fin 3 times the integers sends the three fibres to 3m, 1-3m, and 3m-1. Injectivity and surjectivity cover all integers; the three exponent equalities and parity signs are then proved exactly. The complete Euler HasSum is regrouped by this bijection. The resulting identity is consumed in EulerNineDissection. The underlying Euler pentagonal and Jacobi identities are classical and are supplied by Mathlib and the existing repository products.")),
            Node("0", "continuous_expand", "Positive integral expansion preserves coefficientwise limits and complete sums.", DescribeRole.Theorem),
            Node("1", "pentagonal_sections", "The three complete integer fibres have degrees 3J4, 1+3J2, and 2+3J1.", DescribeRole.Theorem),
            Node("2", "euler_three_sections", "The actual pentagonal Euler series equals J4(q^3)-qJ2(q^3)-q^2J1(q^3).", DescribeRole.Theorem)
        ), []));
    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("eulerpentagonaltrisection-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Question),
            Blocks(Paragraph(Text(text))), role);
}
