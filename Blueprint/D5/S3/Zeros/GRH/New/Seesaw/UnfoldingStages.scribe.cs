using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Seesaw;

internal sealed class UnfoldingStagesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unfolding Stages", H("Unfolding Stages"),
        Blocks(
            Paragraph(Text("Function left after k unfoldings: coefficient of the definite chain; its support.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Seesaw/UnfoldingStages.hasNearLines_of_unfoldStage_ne_zero"),
                H("hasNearLines_of_unfoldStage_ne_zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let φ be a ramified column and y₀ of principal level above g. If the stage-k function is non-zero at a point of U(Y_k), the lines of its lattice move at most k steps above Q and not elsewhere (Grading.HasNearLines).")))))));
}
