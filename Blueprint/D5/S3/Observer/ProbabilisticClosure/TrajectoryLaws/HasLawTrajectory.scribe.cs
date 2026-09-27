using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class HasLawTrajectoryDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Observer/lml2026trajectory");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Own-history conditional distributions determine the trajectory law.",
        H("Own-history conditional distributions determine the trajectory law"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lml2026trajectory"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/HasLawTrajectory.has_law_traj_measure"),
                H("Own-history conditional distributions determine the trajectory law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For any measurable sample space with a finite measure, measurable coordinates with the specified initial probability law and own-history conditional distributions have the corresponding Ionescu--Tulcea trajectory law.")),
                    Paragraph(Text("The initial law is a probability measure; the actual sample measure need only be finite. Coordinates may have dependent measurable types. Each successor conditional law is given the coordinates through the current time. The finite-history induction and projective-limit uniqueness identify the complete trajectory distribution."))),
                DescribeRole.Theorem))));
}
