using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting;

internal sealed class GuardedBoxPathsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Guarded Box Paths.",
        H("Guarded Box Paths"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("guardedboxpaths-endpoint-counts"),
                DeclarationHandle.Create("D5/S0/Rewriting/GuardedBoxPaths.endpoint_counts"),
                H("Signed coordinate displacement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A unit instruction increases one natural coordinate below its capacity, or decreases "
                    + "one positive coordinate. Evaluation proceeds from left to right and fails when a guard "
                    + "fails. For any successfully evaluated word, the integer difference between final and "
                    + "initial values of each coordinate equals its number of increases minus its number of decreases."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("guardedboxpaths-path-lower-bound"),
                DeclarationHandle.Create("D5/S0/Rewriting/GuardedBoxPaths.path_lower_bound"),
                H("Coordinate lower bounds and equality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite coordinate set, a legal word starts inside the capacity box and every "
                    + "instruction passes its guard. Each coordinate receives at least the absolute difference "
                    + "between its endpoint values in instructions. The word length is the sum of the coordinate "
                    + "counts and is at least the sum of the absolute differences. Equality holds exactly when "
                    + "every instruction on each coordinate has the direction of its endpoint difference and "
                    + "the coordinate count equals that absolute difference. A coordinate with equal endpoints "
                    + "then receives no instructions. The argument uses the signed count identity without "
                    + "deleting or reordering instructions."))),
                DescribeRole.Theorem))));
}
