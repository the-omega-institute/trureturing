using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Convexity;

internal sealed class StrongConcavityAttainmentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive strong concavity gives an actual unique maximizer on a complete convex "
        + "domain, without a compactness or finite dimension premise.",
        H("Strong Concavity Attainment"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strong-concavity-complete-attainment"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Convexity/StrongConcavityAttainment.exists_unique_maximizer"),
                H("A unique maximum from completeness and strong concavity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let E be any real normed vector space, s a nonempty complete subset, "
                        + "and f:E->R an upper semicontinuous function on s. Assume that f is "
                        + "m-strongly concave on s for a real m>0 and that f(s) is bounded "
                        + "above. The StrongConcaveOn premise includes convexity of s. "
                        + "There is a point x in s attaining the maximum of f. For every "
                        + "y in s, (m/4)*norm(y-x)^2 <= f(x)-f(y), and every maximizer in "
                        + "s equals x. The norm is the actual norm of E.")),
                    Paragraph(Text(
                        "Choose values of f in its actual image tending to the finite "
                        + "supremum M, and choose their preimages u(n) in s. Midpoint strong "
                        + "concavity bounds m*norm(u(p)-u(q))^2/8 by the average of the two "
                        + "supremum deficits. Once both deficits are below m*epsilon^2/16, "
                        + "the distance is below epsilon. Thus u is Cauchy. Completeness "
                        + "of s gives a limit x in s, and upper semicontinuity forces "
                        + "M<=f(x). The reverse inequality follows from the supremum. "
                        + "Apply the same midpoint estimate at x and y to obtain the "
                        + "quadratic deficit bound and uniqueness.")),
                    Paragraph(Text(
                        "Ambient completeness, finite dimension, compactness of s, "
                        + "boundedness of s, positivity of f, and differentiability of f "
                        + "are not hypotheses. The coefficient m/4 is the midpoint bound; "
                        + "no sharp coefficient is asserted. The strong concavity constant "
                        + "must be strictly positive, and the function is real valued.")),
                    Paragraph(Text(
                        "This standard convex-analysis construction composes Mathlib's "
                        + "StrongConcaveOn, supremum approximation, Cauchy completeness "
                        + "and semicontinuity results. In a quantum entropy application, "
                        + "one must still establish the actual trace-norm carrier, finite "
                        + "entropy boundedness, entropy continuity and quantitative strong "
                        + "concavity. This theorem alone does not prove compactness of "
                        + "a family of quantum states, a common reference state, or an "
                        + "all-temperature Hamiltonian; no literature novelty is claimed."))),
                DescribeRole.Theorem))));
}
