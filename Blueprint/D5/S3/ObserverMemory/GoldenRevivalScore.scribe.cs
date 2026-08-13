using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory;

internal sealed class GoldenRevivalScoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "Fibonacci golden return scores converge to the sharp quadratic-irrational constant.",
            H("Golden Fibonacci Revival Score"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("golden-fibonacci-revival-score-limit"),
                    DeclarationHandle.Create(
                        "D5/S3/ObserverMemory/GoldenRevivalScore."
                        + "golden_fibonacci_revival_score_tendsto"),
                    H("Fibonacci revival scores tend to one over square root five"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Lim, Underscore, Grp(F.Id("n"), To, Infty), Sp,
                        F.Id("F"), Underscore, F.Id("n"), Sp,
                        Lvert, Sp, F.Id("F"), Underscore, F.Id("n"), Sp,
                        Varphi, Sp, Minus, Sp, F.Id("F"), Underscore,
                        Grp(F.Id("n"), Plus, D(1)), Rvert, Sp, Eq, Sp,
                        Frac, Grp(D(1)), Grp(Sqrt, Grp(D(5))), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "At the Fibonacci return time F_n, the scaled golden return error is "
                        + "F_n times the absolute difference between F_n times the golden ratio "
                        + "and F_(n+1). Binet's formula and the exact contracting residual reduce "
                        + "this score to a geometric correction of 1/sqrt(5), whose correction "
                        + "vanishes. This closes only the Fibonacci extremal subsequence; the full "
                        + "spectrum classification and global optimality remain unresolved."))),
                    DescribeRole.Theorem))));
}
