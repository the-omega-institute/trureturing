using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class ExpRemainderDifferencesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/sitnik1993expremainder");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Forward differences of consecutive exponential remainder ratios.",
        H("A negative third forward difference"), Blocks(
            Entry("exponential-remainder", "R", "Exponential Taylor remainders",
                "For each natural n and real x, R(n,x) is exp(x) minus the sum of x to the k divided by k factorial over k from zero through n. This is the remainder after the Taylor polynomial of degree n.",
                DescribeRole.Definition),
            Entry("consecutive-remainder-ratio", "g", "Consecutive remainder ratios",
                "For each natural n and real x, g(n,x) is R(n-1,x) divided by R(n,x). The assertion below uses n at least one and positive x, so natural subtraction agrees with the preceding remainder index.",
                DescribeRole.Definition),
            Entry("all-forward-differences-nonnegative", "claim", "The universal nonnegativity assertion",
                "Source, problem 11 of Sitnik's exponential remainder paper, PDF page 28: «11. Определим функцию при x > 0. gₙ(x) = Rₙ₋₁(x)/Rₙ(x). Исследовать, при каких k разности этой функции при любом фиксированном x неотрицательны ∆ᵏgₙ(x) > 0? Гипотеза: при любых k.» In English: define g(n,x) = R(n-1,x)/R(n,x) for x > 0; for which k are the differences of this function, at every fixed x, nonnegative; conjecture: for all k. The assertion here says that for every natural k and n at least one, and every positive real x, the k-fold iterate of Mathlib's forward difference operator fwdDiff with step one, applied to the sequence m mapped to g(m,x) and evaluated at n, is nonnegative. A negative value also contradicts the strict positivity printed in the source.",
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("exponential-remainder-differences-refutation"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRemainderDifferences.result"),
                H("The universal assertion is false"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("At order three, index one and argument one, the forward difference is strictly negative. Mathlib's binomial expansion expresses it as g(4,1) minus three times g(3,1) plus three times g(2,1) minus g(1,1). The five Taylor remainders are exp(1) minus 1, 2, 5/2, 8/3 and 65/24. The bounds 2.7182818283 < exp(1) < 2.7182818286 make every denominator positive and bound each ratio rationally; the bounds combine to a negative value. This contradicts universal nonnegativity."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("sitnik-1993-exponential-remainder-differences"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/ExpRemainderDifferences." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);
}
