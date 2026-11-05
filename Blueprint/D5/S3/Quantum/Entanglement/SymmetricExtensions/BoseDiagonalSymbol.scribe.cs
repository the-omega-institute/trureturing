using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.SymmetricExtensions;

internal sealed class BoseDiagonalSymbolDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDiagonalSymbol.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex coherent symbols of occupation-diagonal operators", H("Complex coherent symbols of occupation-diagonal operators"), Blocks(
            Paragraph(Text("The operator-polynomial arguments are prior Gulati-Nechita-Park mathematics. The application note has byline Haobo Ma then Wenlin Zhang. Strict hierarchy inclusions, unrestricted witness lifting, and closedness of the unclosed DPS dual sum are outside these statements.")),
            Describe.Lean(DescribeId.Create("bosediagonalsymbol-occupationForm"),
                DeclarationHandle.Create(Prefix + "occupationForm"),
                H("Original occupation polynomial"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/gnp2025dickeextensions")),
                Blocks(Paragraph(Text("The real coefficients sum the actual computational entries with equal row and column occupations. Its squared-variable expansion is the real coherent symbol of the actual occupation twirl."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bosediagonalsymbol-coherent-of-even-realSymbol"),
                DeclarationHandle.Create(Prefix + "coherent_of_even_realSymbol"),
                H("All complex coherent vectors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/gnp2025dickeextensions")),
                Blocks(Paragraph(Text("If an occupation-diagonal Hermitian tensor operator has real symbol p(X squared), then its actual complex coherent quadratic form is p evaluated at the squared complex moduli. Equality on a finite sample is never substituted for this polynomial and all-vector identity."))), DescribeRole.Theorem))));
}
