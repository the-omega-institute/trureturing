using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.IncompleteBeta;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/karp2016incompletebeta");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict positivity of the normalized incomplete beta Turanian coefficients.",
        H("Coefficient convolution and shape imbalance"), Blocks(
            Describe.Lean(DescribeId.Create("incomplete-beta-convolution-imbalance"),
                DeclarationHandle.Create("D5/S3/Analytic/IncompleteBeta/Result.convolution_strictAnti_imbalance"),
                H("Strict decrease of the convolution"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For positive real a and m and every natural n, the sum over k from zero to n of c(k,a,m+d)c(n-k,a,m-d) is strictly decreasing as d ranges from zero, included, to m, excluded. Here c(j,a,b) is Gamma(a+b+j) divided by Gamma(b)Gamma(a+j+1). Thus the convolution decreases with the absolute difference of the two positive shape parameters when their sum is fixed.")),
                    Paragraph(Text("Termwise beta integration expresses the convolution as Gamma(2a+2m+n)/Gamma(2m) times the normalized beta mean of W. The kernel W(u) is the sum over k from zero to n of u to the power a+k times (1-u) to the power a+n-k, divided by Gamma(a+k+1)Gamma(a+n-k+1). Reflection of the finite sum makes W symmetric. Differentiating each summand gives two adjacent terms whose sum telescopes. The derivative equals [u(1-u)] to the power a-1 times [(1-u) to the power n+1 minus u to the power n+1], divided by Gamma(a)Gamma(a+n+1). It is positive between zero and one half. All kernel powers have positive exponents, so W is continuous at both endpoints. The strict beta comparison therefore applies, with a common positive Gamma factor."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("incomplete-beta-positive-turanian-coefficients"),
                DeclarationHandle.Create("D5/S3/Analytic/IncompleteBeta/Result.result"),
                H("Positive coefficients for all positive shifts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every positive real a, b, alpha and beta and every natural n, the sum over k from zero to n of c(k,a,b+alpha)c(n-k,a,b+beta) minus c(k,a,b)c(n-k,a,b+alpha+beta) is strictly positive. These are the coefficients of the normalized incomplete beta Turanian; they are independent of the series variable.")),
                    Paragraph(Text("The two convolutions have the common mean shape b+(alpha+beta)/2. Their nonnegative half differences are respectively the absolute value of alpha-beta divided by two and (alpha+beta)/2. Positivity of both shifts makes the first strictly smaller. Convolution symmetry handles either ordering of the shifts, and strict decrease with imbalance gives the asserted positive difference."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("karp-2016-incomplete-beta-coefficient-log-concavity"),
                    ResolutionKind.Proved)))));
}
