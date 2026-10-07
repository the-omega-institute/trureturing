using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase.LonelyRunnerDeletion;

internal sealed class OneDeletionDefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The one-deletion question uses a supremum over all real times of nearest-integer distance.",
        H("The Lonely Runner value and one-deletion statement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lonely-value"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/LonelyRunnerDeletion/OneDeletionDefs.lonelyValue"),
                H("The Lonely Runner value"),
                StatementSource.FromAuthor(Disp(FormulaDsl.Id("lonelyValue"))),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Dynamics/zhang2026lonelyrunnerdeletion")),
                Blocks(Paragraph(Text(
                    "For a finite set V of natural speeds, lonelyValue V is the supremum over "
                        + "all real times t of the infimum over v in V of |v*t - round(v*t)|. "
                        + "This is the distance of each runner from the nearest integer."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("one-deletion-claim"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/LonelyRunnerDeletion/OneDeletionDefs.claim"),
                H("The fixed one-deletion claim"),
                StatementSource.FromAuthor(Disp(FormulaDsl.Id("claim"))),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Dynamics/zhang2026lonelyrunnerdeletion")),
                Blocks(Paragraph(Text(
                    "The claim quantifies over every N >= 2 and every 1 <= r <= N. "
                        + "It requires the lower bound 1/N for Finset.Icc 1 N with r erased, "
                        + "and characterizes equality by r = N or N = 2. The boundary N = 2 "
                        + "includes both singleton deletion choices."))),
                DescribeRole.Definition))));
}
