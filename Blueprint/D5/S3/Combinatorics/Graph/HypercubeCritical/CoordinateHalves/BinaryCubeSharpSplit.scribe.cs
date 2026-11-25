using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves;

internal sealed class BinaryCubeSharpSplitDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSharpSplit";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Opposite-section sums attain the six-cube minimum, with disjoint section supports within each pair.",
        H("Equality in the two-coordinate split bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-section"),
                DeclarationHandle.Create(Module + ".twoSection"),
                H("Section at two fixed coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix the first two bits of a binary word on Q(n + 2) to a and b. The remaining n bits index " +
                        "the section."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sites-card-two-sections"),
                DeclarationHandle.Create(Module + ".sites_card_two_sections"),
                H("The four section sizes add to the total weight"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Each supported vertex belongs to exactly one section, so the total weight is the sum of the " +
                        "four support sizes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sharp-split"),
                DeclarationHandle.Create(Module + ".sharp_split"),
                H("Two nonzero opposite sums force a sharp split"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let f be a Q8 binary kernel word of weight at most twelve. Assume both opposite-section sums " +
                        "00 + 11 and 10 + 01 are nonzero. Then f has weight exactly twelve. Each sum has support a " +
                        "full Q6 neighbor shell, and within each opposite pair the two section supports are disjoint.")),
                    Paragraph(Text("Adding opposite section equations cancels the terms from the other pair, leaving a Q6 kernel " +
                        "word. Each nonzero sum has weight at least six. The budget of twelve is therefore exhausted " +
                        "by the two sums, and the binary support identity forces both overlaps to vanish. The " +
                        "minimum-support classification identifies both sums."))),
                DescribeRole.Theorem)),
        []));
}
