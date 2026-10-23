using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EllipticTailExponent;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/baowangqiu2022ellipticparameter");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The supremum of the elliptic remainder exponent", H("The exact bound for every truncation"), Blocks(
            Describe.Lean(DescribeId.Create("elliptic-tail-exponent-denominator-pos"),
                DeclarationHandle.Create("D5/S3/Analytic/EllipticTailExponent/Result.denominator_pos"),
                H("Positive remainder denominator"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural n and 0<a<=1/2, sin(pi a)-pi(1-a)S(n,a) is strictly positive. The coefficient-tail identity factors the remainder as a^2 U(n,a), whose factors are positive."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("elliptic-tail-exponent-lambda10-eq"),
                DeclarationHandle.Create("D5/S3/Analytic/EllipticTailExponent/Result.lambda10_eq"),
                H("Logarithmic derivative identity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural n and 0<a<=1/2, the parameter exponent equals 2+a U'(n,a)/U(n,a). The finite Euler product identifies each summand as a^2 b(k,a). The sine remainder is therefore a^2 U(n,a). Both functions are differentiable near each positive parameter. Equality of their derivatives within (0,1/2] includes the endpoint a=1/2, and the quotient rule gives the stated exponent."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("elliptic-tail-exponent-lambda10-lt-two"),
                DeclarationHandle.Create("D5/S3/Analytic/EllipticTailExponent/Result.lambda10_lt_two"),
                H("Strict upper bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural n and 0<a<=1/2, the parameter exponent is strictly below two. The correction a U'(n,a)/U(n,a) is strictly negative because U is positive and its derivative is negative."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("elliptic-tail-exponent-tendsto-lambda10"),
                DeclarationHandle.Create("D5/S3/Analytic/EllipticTailExponent/Result.tendsto_lambda10"),
                H("The limiting exponent at zero"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural n, the parameter exponent tends to two as a decreases to zero through positive values. The uniform derivative bound gives a U'(n,a) tending to zero, while continuity and U(n,0)=1/(n+1) give a positive denominator limit."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("elliptic-tail-exponent-result"),
                DeclarationHandle.Create("D5/S3/Analytic/EllipticTailExponent/Result.result"),
                H("The exact supremum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural n, two is the least upper bound of the values of the parameter exponent on (0,1/2]. Each value is strictly smaller than two, and the right-hand limit at zero places two in the closure of this set of values."))), DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bao-wang-qiu-2022-elliptic-tail-exponent"),
                    ResolutionKind.Proved)))));
}
