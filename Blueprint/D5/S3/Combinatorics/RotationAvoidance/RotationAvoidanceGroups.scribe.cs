using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceGroupsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceGroups.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Representative circular avoidance classes have explicit cardinalities and strict comparisons.",
        H("RotationAvoidanceGroups"),
        Blocks(
            Node("rotationavoidancegroups-circularrepresentativecounts", "Circular representative counts", "circular_representative_counts", "For positive size, the circular avoider classes on size plus one entries have the following cardinalities: the 1234 class is 2 to the size plus one minus twice size minus one minus the binomial coefficient choosing three from size plus one; the 1432 and 2143 classes equal it; the 1342 class is 2 to the size minus size; the 1243 class equals the 1342 class; the 1324 class is the Fibonacci number with index twice size minus one; the 1423 and 2413 classes equal the 1324 class. When size is at least five, the 1342 class is smaller than the 1234 class, which is smaller than the 1324 class.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}

