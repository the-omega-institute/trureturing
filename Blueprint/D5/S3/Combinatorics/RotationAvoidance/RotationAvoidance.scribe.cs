using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidance.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rotation avoidance has exactly eight Wilf classes for patterns of length four.",
        H("RotationAvoidance"),
        Blocks(
            Node("rotationavoidance-result", "Eight Wilf classes", "result", "For every integer k at least four and all patterns q and s that permute one through four, the numbers of permutations of one through n whose first k rotations avoid q and s agree for every n at least k if and only if s is q, its complement, its reverse, or the complement of its reverse. The eight classes are represented by 1234, 1243, 1324, 1342, 1423, 1432, 2143 and 2413. Complement and reversal give equal counts within each orbit; circular counts and strict inequalities between counts of circles with one containing cut separate distinct orbits. Sizes six and seven distinguish the cases k equal to four or five. Classical containment is represented by an increasing choice of values whose pattern-ordered list is a subsequence, as in the order-pattern descriptions used for nonnesting and arrow-decorated permutations.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
