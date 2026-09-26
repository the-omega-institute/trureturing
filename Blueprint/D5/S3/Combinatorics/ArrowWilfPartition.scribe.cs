using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArrowWilfPartitionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArrowWilfPartition.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/zhou2026arrow");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Avoiding words partition according to whether a fixed point exists and, if so, its largest or smallest value.",
        H("Partitions by Extremal Fixed Points"),
        Blocks(
            Node("avoiding-words", "Words satisfying a predicate", "Avoiding", "Avoiding(s,P) is the subtype of words on s satisfying P.", DescribeRole.Definition),
            Node("largest-fixed-fiber", "The largest-fixed-point fiber", "MaxFixedFiber", "A word in this fiber satisfies P, fixes m under hat, and fixes no value of s larger than m.", DescribeRole.Definition),
            Node("smallest-fixed-fiber", "The smallest-fixed-point fiber", "MinFixedFiber", "A word in this fiber satisfies P, fixes m under hat, and fixes no value of s smaller than m.", DescribeRole.Definition),
            Node("largest-partition-map", "Map to the largest fixed point", "maxFixedPartitionMap", "The map sends an avoiding word either to the no-fixed-point case or to the fiber indexed by its largest hat-fixed value.", DescribeRole.Definition),
            Node("largest-partition-equivalence", "Partition by largest fixed point", "maxFixedPartitionEquiv", "When all no-fixed-point words satisfy P, avoiding words are equivalent to the sum of NoFixed(s) and all largest-fixed-point fibers.", DescribeRole.Definition),
            Node("smallest-partition-map", "Map to the smallest fixed point", "minFixedPartitionMap", "The map sends an avoiding word either to the no-fixed-point case or to the fiber indexed by its smallest hat-fixed value.", DescribeRole.Definition),
            Node("smallest-partition-equivalence", "Partition by smallest fixed point", "minFixedPartitionEquiv", "When all no-fixed-point words satisfy P, avoiding words are equivalent to the sum of NoFixed(s) and all smallest-fixed-point fibers.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
