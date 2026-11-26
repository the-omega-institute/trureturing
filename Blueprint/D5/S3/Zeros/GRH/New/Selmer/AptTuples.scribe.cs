using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class AptTuplesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Apt Tuples", H("Apt Tuples"),
        Blocks(
            Paragraph(Text("Divisibility and counting bookkeeping at the level; lattice versus representation dictionary. Basic properties of apt label tuples and their idempotents; a place off the level.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/AptTuples.exists_algHom"),
                H("exists_algHom"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If u is a lattice in R over O, some injective O-algebra map F from matrices over O to matrices over ℚ̄_ℓ sends u(g) to R(g) and preserves determinants and traces.")))))));
}
