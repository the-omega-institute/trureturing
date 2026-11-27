using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Groups;

internal sealed class IrreducibleCharactersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Irreducible Characters", H("Irreducible Characters"),
        Blocks(
            Paragraph(Text("Recognising irreducible and virtual characters by pairings; when a character's projector vanishes.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Groups/IrreducibleCharacters.groupAlgElem_eq_zero"),
                H("groupAlgElem_eq_zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let G be finite, i : G → H a homomorphism, χ a character of H, s ∈ H, ρ a finite-dimensional complex representation of G. If the average over G of χ(i(g))·tr ρ(g) vanishes, then ∑_g χ(i(g)s)·ρ(g) = 0.")))))));
}
