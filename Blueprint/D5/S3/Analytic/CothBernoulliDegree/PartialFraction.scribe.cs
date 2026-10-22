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
                DescribeRole.Theorem))));
}
