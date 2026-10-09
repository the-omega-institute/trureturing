using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Games;

internal sealed class DivisorNimBoundSmallDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Games/DivisorNimBoundSmall.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Paired dyadic remainders sharpen the bounds for small distinguished heaps.",
        H("Distinguished Heaps Two and Four"),
        Blocks(
            Node("dnim-divisornimboundsmall-0", "Discard bounded exceptional removals", "refined_step",
                "Low-depth removals are bounded by B. Any higher-depth removal with nonzero value must change a unique minimum-depth heap. If its value exceeds B, counting its possible amounts in A bounds the current value by B plus the cardinality of A plus one.", DescribeRole.Theorem),
            Node("dnim-divisornimboundsmall-1", "A paired minimum-depth remainder", "paired_remainder_zero",
                "If the other heaps have minimum-depth count one at depth k and a legal removal leaves a positive heap at depth k, the follower has count two and value zero.", DescribeRole.Theorem),
            Node("dnim-divisornimboundsmall-2", "The two largest dyadic divisors", "power_divisor_high",
                "A divisor of two to the power k plus one whose valuation is at least k equals either two to the power k or two to the power k plus one.", DescribeRole.Theorem),
            Node("dnim-divisornimboundsmall-3", "One exceptional removal remains", "paired_pivot_bound",
                "When a pivot at depth k lies beside a unique heap at depth k plus one, subtracting two to the power k produces a zero follower. A reference heap of size two to the power k plus one leaves only one higher removal to count; lower followers bounded by B give the bound B plus two.", DescribeRole.Theorem),
            Node("dnim-divisornimboundsmall-4", "Apply the paired pivot after a lower move", "lower_paired_bound",
                "Changing a higher-depth heap by two to the power k beneath a unique depth k plus one heap creates the paired-pivot configuration. If its lower followers have value at most B, its value is at most B plus two.", DescribeRole.Theorem),
            Node("dnim-divisornimboundsmall-5", "No unique minimum-depth heap", "multiple_step",
                "When the minimum-depth count is not one, a nonzero position has only zero higher-depth followers. A bound B on lower-depth followers gives value at most B plus one.", DescribeRole.Theorem),
            Node("dnim-divisornimboundsmall-6", "Seven beside one depth-one heap", "seven_bound",
                "A board containing seven, with all other heaps even and exactly one at depth one, has value at most six. Removals one and five on seven both give zero; all removals on other heaps give zero.", DescribeRole.Theorem),
            Node("dnim-divisornimboundsmall-7", "A distinguished heap of size two", "two_bound",
                "Every positive position containing a heap of size two has value at most four, regardless of the other heap sizes and their number.", DescribeRole.Theorem),
            Node("dnim-divisornimboundsmall-8", "Odd removals beside four", "four_lower_odd",
                "From a positive-depth board containing four, every odd removal produces a follower of value at most four. The reference heap either remains four or becomes a positive odd heap at most three.", DescribeRole.Theorem),
            Node("dnim-divisornimboundsmall-9", "A distinguished heap of size four", "four_bound",
                "Every positive position containing a heap of size four has value at most eight. The unique-depth case uses the paired pivot after a removal of size two.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
