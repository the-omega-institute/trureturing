using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.DualPair;

internal sealed class DescentsVanishDefDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Descents Vanish Def", H("Descents Vanish Def"),
        Blocks(
            Paragraph(Text("Predicate: all theta descents with data vacuum at given places vanish.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/DualPair/DescentsVanishDef.DescentsVanish"),
                H("DescentsVanish"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("All descents g ↦ ∫θ(ω_{a,1}(g,h)f)Y(h)dh of Y from U(V) to U(W) vanish, for data f that are the vacuum at the places of S ∪ S̄.")))))));
}
