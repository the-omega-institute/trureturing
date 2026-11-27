using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.WachGamma;

internal sealed class LettersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Letters", H("Letters"),
        Blocks(
            Paragraph(Text("Functoriality of Kisin modules, projectors to embeddings, pole orders of invariant forms.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/WachGamma/Letters.formsOfType_subset_pred_of_notMem"),
                H("formsOfType_subset_pred_of_notMem"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If n is not in the set U_i of allowed jumps, every invariant form with pole order at most n on the part of L at the letter i has pole order at most n − 1 there.")))))));
}
