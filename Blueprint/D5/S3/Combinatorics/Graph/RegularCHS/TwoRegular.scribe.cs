using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.RegularCHS;

internal sealed class TwoRegularDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete homogeneous coefficient domination for two-regular graphs.",
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
                    Paragraph(Text("The comparison is preserved by substitution of the odd Catalan series and multiplication by the common nonnegative numerator. These operations connect the factors to the complete homogeneous coefficients of cycle components."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("regular-chs-two-regular"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/RegularCHS/TwoRegular.chs_cycle_le_twoRegular"),
                H("Cycle domination for two-regular graphs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/GraphInvariants/chavez2023extremalpolynomialnorms")),
                Blocks(Paragraph(Text("For every two-regular simple graph on n vertices, with n at least three, every adjacency complete homogeneous coefficient is at least the corresponding coefficient of the cycle on n vertices. The graph may be disconnected and the degree of the coefficient may be odd or zero.")),
                    Paragraph(Text("Degree two passes to each connected component through an explicit equivalence of neighbor sets. Each component contains a cycle, and the connected degree-two cycle-isomorphism theorem in the Brooks module identifies that component with a cycle of length at least three. The component lengths sum to n, and the adjacency pencil determinant factors over the components.")),
                    Paragraph(Text("Let q be the odd Catalan series, which satisfies q = t times (1 plus q squared). The cleared adjacency pencil of a cycle of length l has determinant (1 minus q to the power l) squared. The Hermitian determinant formula and the complete homogeneous series product identify the graph series with (1 plus q squared) to the power n times the product of the substituted cycle factors. The single cycle has the same numerator and the factor at the sum of the component lengths. The coefficient partition theorem, nonnegative substitution, and multiplication by the common numerator prove the comparison."))),
                DescribeRole.Theorem))));
}
