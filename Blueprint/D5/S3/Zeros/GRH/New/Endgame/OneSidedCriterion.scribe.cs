using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Endgame;

internal sealed class OneSidedCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One Sided Criterion", H("One Sided Criterion"),
        Blocks(
            Paragraph(Text("One-sided bound gives a zero-free half-plane; small value in every long window.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Endgame/OneSidedCriterion.exists_window_sub_mul_le"),
                H("exists_window_sub_mul_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If E and E' are polar (IsPolar), then for all large t and every X in [0, e^t] there is u in [t, t²] with E(u) − X E'(u) ≤ e^{−t}.")))))));
}
