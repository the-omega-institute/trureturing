using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.Crystalline;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Defs", H("Defs"),
        Blocks(
            Paragraph(Text("Definitions: (potentially) crystalline, Hodge–Tate jumps, Weil pairs, linear Frobenius, crystalline cocycles.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/Crystalline/Defs.isWeilPair_zero_iff"),
                H("isWeilPair_zero_iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For s in G_p, (s, 0) is a Weil pair if and only if s lies in the inertia group of the valuation ring of Q̄_p.")))))));
}
