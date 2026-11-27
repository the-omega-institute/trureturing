using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class ReciprocityLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reciprocity Law", H("Reciprocity Law"),
        Blocks(
            Paragraph(Text("A value of an even class vanishes if all its cyclic images vanish. Odd Kummer-type maps with reciprocity law against even classes, primitive, with prescribed zeros.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/ReciprocityLaw.exists_isLaw"),
                H("exists_isLaw"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let E be stably unramified with ≥ 4 infinite places, r ≥ 1. Given Frobenii x_i fixing μ_{ℓ^r}, at degree-one places off ℓ over distinct primes of E⁺, and at most as many y_i, some function z with IsLaw kills all y_i and takes a unit value on an element fixing μ_{ℓ^r}.")))))));
}
