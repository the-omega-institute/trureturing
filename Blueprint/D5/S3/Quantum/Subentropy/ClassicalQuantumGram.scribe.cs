using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Subentropy;

internal sealed class ClassicalQuantumGramDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Subentropy/ClassicalQuantumGram.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Entropy/datta2014subentropy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Square-root Gram realization of canonical classical-quantum record states.",
        H("Classical-quantum Gram realization"),
        Blocks(
            Paragraph(Text("The label and fragment coordinate types are arbitrary finite types. Zero probabilities, singular conditional states, repeated eigenvalues and different row and column dimensions are permitted. For Y_x=p_x rho_x, form the rectangular matrix V whose x-th column block is the positive square root of Y_x. Its two Gram products are used without identifying their ambient spaces.")),
            Item("blockPinch", "Coordinate block pinching", "The map retains a matrix entry precisely when its two classical labels agree.", DescribeRole.Definition),
            Item("cqRowSqrt", "Rectangular row of square roots", "The row block indexed by x is the positive square root of p_x rho_x.", DescribeRole.Definition),
            Item("conditionalSubentropy", "Canonical conditional subentropy", "Conditional subentropy is subentropy(recordState) minus subentropy(mixtureState).", DescribeRole.Definition))));

    private static DocumentBlock.Describe Item(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Owner + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(text))), role);
}
