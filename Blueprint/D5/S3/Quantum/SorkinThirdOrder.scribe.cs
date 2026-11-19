using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class SorkinThirdOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quadratic branch weights have no third-order inclusion-exclusion term.",
        H("Sorkin Third-Order Cancellation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quadratic-amplitude-branch-weight"),
                DeclarationHandle.Create("D5/S3/Quantum/SorkinThirdOrder.amplitudeWeight"),
                H("Quadratic amplitude branch weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite branch family over a commutative star ring, the weight "
                    + "is the product of the amplitude sum and its star conjugate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sorkin-third-order-cancellation"),
                DeclarationHandle.Create("D5/S3/Quantum/SorkinThirdOrder.sorkin_third_order_cancellation"),
                H("Sorkin third-order cancellation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For pairwise disjoint finite branch families A, B and C, the alternating "
                    + "sum of the quadratic weights of A∪B∪C, its three pair unions, and its "
                    + "three singleton unions is zero. The proof is the cancellation of all "
                    + "self and pairwise cross terms after expanding the quadratic amplitude."))),
                DescribeRole.Theorem))));
}
