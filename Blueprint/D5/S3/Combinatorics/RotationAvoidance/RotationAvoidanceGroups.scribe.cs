using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceGroupsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceGroups.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three circular representative classes have uniformly separated cardinalities.",
        H("RotationAvoidanceGroups"),
        Blocks(
            Node("rotationavoidancegroups-circularrepresentativeseparations", "Strict separation of three circular classes", "circular_representative_separations", "For size at least five, the number of circular permutations of one through size plus one rooted at one and avoiding 1342 is strictly smaller than the number avoiding 1234, which is strictly smaller than the number avoiding 1324. Cutting at the minimum and increasing relabelling identify these circular classes with classical avoidance classes. Their counts are 2^size minus size, 2^(size + 1) minus twice size minus one minus the binomial coefficient choosing three from size plus one, and F_(2 size - 1), respectively. Exponential bounds and a Fibonacci recurrence give the strict comparisons.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

