using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.ExceptionCount;

internal sealed class ReductionArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite arithmetic bounds for exception counting.",
        H("Arithmetic reduction to prime prefixes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("robin-product-upper"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/ExceptionCount/ReductionArithmetic.robin_product_upper"),
                H("Mertens product upper bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The divisor ratio is at most the canonical finite Mertens product when the cutoff contains at least as many primes as the support of n. This identifies the arithmetic bound with the analytic product used for the strict logarithmic gap."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kappa-product-tail-upper"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/ExceptionCount/ReductionArithmetic.kappa_product_tail_upper"),
                H("Uniform kappa product bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive delta there is a nonnegative constant C such that, for kappa at least 1+delta, P at least 2, n nonzero, and omega(n) at most pi(P), the bound zeta(kappa) sigma^[kappa](n) / n^kappa <= (M(P) * exp(C P^(-delta/2)))^kappa holds uniformly in kappa, P, and n, where M(P) is the finite Mertens product. The proof separates the omitted Euler factors and uses the uniform logarithmic tail estimate."))),
                DescribeRole.Theorem))));
}
