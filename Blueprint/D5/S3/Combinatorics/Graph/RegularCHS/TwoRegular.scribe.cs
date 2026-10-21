using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.RegularCHS;

internal sealed class TwoRegularDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cycle denominator coefficients and positive length partitions.",
        H("Cycle partitions"), Blocks(
            Describe.Lean(DescribeId.Create("regular-chs-cycle-kernel"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/RegularCHS/TwoRegular.cycleKernel"),
                H("The squared geometric cycle factor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/GraphInvariants/chavez2023extremalpolynomialnorms")),
                Blocks(Paragraph(Text("The series cycleKernel l is obtained from the series with coefficient k plus one by substituting X to the power l. For positive l its coefficient in degree k equals k divided by l plus one when l divides k, and zero otherwise; the division is natural-number division."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("regular-chs-cycle-partition"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/RegularCHS/TwoRegular.cycleKernel_sum_le_prod"),
                H("Partitioning a cycle length increases denominator coefficients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/GraphInvariants/chavez2023extremalpolynomialnorms")),
                Blocks(Paragraph(Text("For any nonempty finite list of positive lengths, every coefficient of the cycle factor at their sum is at most the corresponding coefficient of the product of their cycle factors. To merge two lengths a and b, a nonzero coefficient on the left has degree (a+b)j and value j+1. The convolution on the right contains the term with degrees aj and bj, whose value is (j+1) squared. All other terms are nonnegative. Induction merges any finite partition.")),
                    Paragraph(Text("This comparison concerns formal denominator factors. Connecting them to the adjacency complete homogeneous coefficients of a two-regular graph requires a cycle decomposition and the generating function identity."))),
                DescribeRole.Theorem))));
}
