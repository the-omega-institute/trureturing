using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Witt;

internal sealed class MaximalCompactDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Maximal Compact", H("Maximal Compact"),
        Blocks(
            Paragraph(Text("Block embedding of U(Y) into U(Y ⊕ Y'). Maximal compact subgroup of the adelic unitary group and its compactness.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Witt/MaximalCompact.maxCompact"),
                H("maxCompact"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The subgroup K_∞K₀ of G: elements that are unitary matrices at each infinite place and lie in GL_n(Ô) at the finite places.")))))));
}
