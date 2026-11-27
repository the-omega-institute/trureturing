using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Groups;

internal sealed class RatModIntDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rat Mod Int", H("Rat Mod Int"),
        Blocks(
            Paragraph(Text("Basic facts on Q/Z; character group of a finite abelian group.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Groups/RatModInt.card_hom_QZ"),
                H("card_hom_QZ"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("A finite abelian group A has exactly #A homomorphisms to ℚ/ℤ: its Pontryagin dual has the same order as A.")))))));
}
