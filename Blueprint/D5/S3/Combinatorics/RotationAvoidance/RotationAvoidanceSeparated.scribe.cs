using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceSeparatedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSeparated.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separated endpoint configurations force alternating middle normal forms and Fibonacci endpoint structure.",
        H("RotationAvoidanceSeparated"),
        Blocks(
            Node("rotationavoidanceseparated-alternatingpositivemiddlenormalform", "Alternating positive middle normal form", "alternating_positive_middle_normal_form", "Let first plus one be less than last and exactly the uncut rotation of a permutation contain 2413. Then first is at least two and last is below size. The interior is the upper filtered list, followed by the middle interval, followed by the lower filtered list. The upper list avoids 213 and 4132, while the lower list avoids 132 and 3241.", DescribeRole.Theorem),
            Node("rotationavoidanceseparated-fibonaccileastendpointnormalform", "Fibonacci least endpoint normal form", "fibonacci_least_endpoint_normal_form", "Let a permutation begin with one and end with last, and suppose exactly the uncut rotation contains 1324. Then last is at least four. The interior is the upper filtered list followed by the lower filtered list; these lists are permutations of their corresponding intervals. The upper list avoids 213 and 4132, the lower list avoids 132 and 213, and the lower list is not strictly increasing.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

