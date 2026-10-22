using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.CothBernoulliDegree;

internal sealed class PartialFractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rational partial fractions for the signed Bernoulli remainder.",
        H("A positive mixture of rational kernels"), Blocks(
            Describe.Lean(DescribeId.Create("coth-bernoulli-partial-fractions"),
                DeclarationHandle.Create("D5/S3/Analytic/CothBernoulliDegree/PartialFraction.P_eq_tsum"),
                H("The series representation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all natural m and n and every positive real t, P(m,n,t) equals twice the sum over natural k of t^(m+2n) divided by (pi(k+1))^(2n) and by t^2+(pi(k+1))^2. Every weight is positive.")),
                    Paragraph(Text("Substitution of an imaginary argument in the cotangent partial fractions gives the case n=0. The even zeta values identify each successive Bernoulli coefficient. Subtraction and the finite geometric identity then give the remainder for every n. All series equalities are obtained from convergent series."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coth-bernoulli-derivative-series"),
                DeclarationHandle.Create("D5/S3/Analytic/CothBernoulliDegree/PartialFraction.hasSum_iteratedDeriv_P"),
                H("Convergence of the derivative series"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural derivative order r and all natural m and n, the series obtained by differentiating the rational kernels r times converges at each positive real t. Its sum is half the r-th derivative of P(m,n) at t.")),
                    Paragraph(Text("The imaginary part of a complex linear reciprocal gives the quadratic reciprocal. Its r-th derivative has absolute value at most r! divided by a^(r+2) for positive a. The product rule gives uniform bounds on bounded real intervals. The resulting majorants are constant multiples of the convergent reciprocal-square series."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coth-bernoulli-iterated-derivative"),
                DeclarationHandle.Create("D5/S3/Analytic/CothBernoulliDegree/PartialFraction.iteratedDeriv_P"),
                H("Differentiation of the representation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural r, the r-th derivative of P(m,n) at a positive t equals twice the sum of the r-th derivatives of the rational kernels with the same weights. This includes all orders through m+2n-1.")),
                    Paragraph(Text("The original remainder agrees with its rational series on a neighborhood of every positive argument. Neighborhood invariance of iterated derivatives transfers the termwise derivative identity to the pinned remainder, without imposing any condition on its value at zero."))),
                DescribeRole.Theorem))));
}
