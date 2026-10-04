using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceOneAscentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceOneAscent.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One-ascent enumeration and interval order constrain unique containing rotations.",
        H("RotationAvoidanceOneAscent"),
        Blocks(
            Node("rotationavoidanceoneascent-one-ascent-count", "Enumeration and avoidance of one-ascent permutations", "one_ascent_count", "For every nonnegative size, the permutations of one through size that are not decreasing but can be split into two decreasing lists number 2^size minus size minus one. Every such permutation avoids 123 and 3412. Thus these are exactly the permutations with one ascent, counted by choosing the entries of their first decreasing block and excluding the decreasing concatenations.", DescribeRole.Theorem),
            Node("rotationavoidanceoneascent-paired-endpoint-color-order", "Order of lower and upper endpoint intervals", "paired_endpoint_color_order", "Let size be at least four. If a permutation begins with first, ends with last, and contains 2143 in exactly the uncut rotation, then first is less than last. The interior entries below first form an increasing list, and those above last form an increasing list. Some interior entry below first precedes an interior entry above last.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
