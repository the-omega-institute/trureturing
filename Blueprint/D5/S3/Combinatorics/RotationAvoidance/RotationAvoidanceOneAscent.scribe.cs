using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceOneAscentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceOneAscent.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Permutations with one ascent split into decreasing parts and supply a lower bound for a classical avoidance class.",
        H("RotationAvoidanceOneAscent"),
        Blocks(
            Node("rotationavoidanceoneascent-oneascentcount", "Count of one-ascent permutations", "one_ascent_count", "For every size, the permutations of one through size that are not wholly decreasing but split at some cut into two decreasing lists number 2 to the size minus size minus one. Every such permutation avoids 123 and 3412.", DescribeRole.Theorem),
            Node("rotationavoidanceoneascent-ascendingoneascentgap", "One-ascent lower bound", "ascending_one_ascent_gap", "For every size, 2 to the size minus size minus one is at most one less than the number of permutations avoiding 123 and 3412. For size at least four, the inequality is strict.", DescribeRole.Theorem),
            Node("rotationavoidanceoneascent-pairedendpointcolororder", "Paired endpoint color order", "paired_endpoint_color_order", "Let a permutation have first and last entries and suppose exactly the uncut rotation contains 2143. Then first is less than last. The entries below first in the interior are increasing, the entries above last in the interior are increasing, and the interior contains an increasing pair whose first value is below first and whose second value is above last.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}

