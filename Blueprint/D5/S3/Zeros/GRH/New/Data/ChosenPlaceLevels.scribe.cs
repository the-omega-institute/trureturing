using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Data;

internal sealed class ChosenPlaceLevelsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Chosen Place Levels", H("Chosen Place Levels"),
        Blocks(
            Paragraph(Text("Chosen places above g, the integer Data.chosenGroupOrder, principal level, trivial stabilisers, sizes.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Data/ChosenPlaceLevels.omega_zpow_ne_one"),
                H("omega_zpow_ne_one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For an integer n with 0 < |n| ≤ 8m and a finite place w of E, the residue character ω_w^n is non-trivial if and only if w is a chosen place (Data.IsChosen).")))))));
}
