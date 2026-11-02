using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class ActualMomentOrderArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact scalar order arithmetic for the original actual-K moment endpoint.",
        H("Actual-K scalar endpoint"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q-scalar-bounds"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualMomentOrderArithmetic.q_scalar_bounds"),
                H("Original moment order scalar bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the original ceiling N(C, alpha, D), with C at least one and D positive, "
                        + "the order is at least one and N/D is at least eight. The exact curvature "
                        + "payment is at most one eighth, and the logarithmic ceiling pays beta plus "
                        + "the Euler and endpoint constants with the retained one fifth margin. The "
                        + "definition keeps the original max, ceiling, inclusive moment degree, and "
                        + "all degenerate finite families."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("leading-one"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualMomentOrderArithmetic.leading_one"),
                H("Original leading-one order asymptotic"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive alpha and C at least one, the original order satisfies "
                        + "log(N/D)/exp(D/2) tending to one as D tends to infinity. The proof "
                        + "retains the original beta, ceiling squeeze, and both decaying exponential "
                        + "terms without asserting a sublinear order or an RH endpoint."))),
                DescribeRole.Theorem))));
}
