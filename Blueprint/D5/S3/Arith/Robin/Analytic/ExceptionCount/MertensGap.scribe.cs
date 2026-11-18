using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.ExceptionCount;

internal sealed class MertensGapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A strict initial-prime Euler product gap absorbs a power-decaying omitted Euler tail.",
        H("Strict Mertens product gap"),
        Blocks(
            Describe.Lean(DescribeId.Create("product"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/ExceptionCount/MertensGap.product"),
                H("Initial-prime inverse product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite inverse Euler product contains exactly the primes at most the real cutoff, including equality at a prime cutoff."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("upper-half-gap"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/ExceptionCount/MertensGap.upper_half_product_gap"),
                H("Upper-half interval gap"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every positive a and every fixed real C, the product at P=exp(t-1/(2t)), multiplied by exp(C P^(-a)), is eventually at most exp(gamma)(t-1/(4t)). The strengthened Mertens error is o(1/t^2) at this cutoff. The extra logarithmic Euler tail is also o(1/t^2), so the exponential perturbation consumes less than half the prescribed gap.")),
                    Paragraph(Text("With t=log(log(x)), this perturbed initial-prime product is eventually strictly less than exp(gamma) log(log(x/2)). The logarithmic tangent inequality bounds the shift from x to x/2 by log(2)/(log(x)-log(2)), which is o(1/log(log(x))). This strict estimate is uniform over every integer in the upper half interval after monotonicity of log(log(n))."))),
                DescribeRole.Theorem))));
}
