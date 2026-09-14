using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class HarmonicGammaTailDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/HarmonicGammaTail.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/nist2026asymptotic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A signed estimate for the harmonic-logarithmic tail gives a rational upper bound for Euler's constant.",
        H("A Signed Harmonic–Logarithmic Tail Estimate"),
        Blocks(
            Paragraph(Text("Let H_N be the sum of the reciprocals of the integers from 1 to N, and let γ be the Euler–Mascheroni constant. The estimate holds for every positive integer N.")),
            Describe.Lean(
                DescribeId.Create("harmonic-log-tail-lower"),
                DeclarationHandle.Create(Prefix + "harmonic_log_tail_lower"),
                H("The signed lower estimate"),
                StatementSource.FromAuthor(LowerFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Set q_N = H_N − log N − 1/(2N) + 1/(12N²). Its consecutive difference is f(N), where f(x) = log(x+1) − log x − 1/(2x) − 1/(2(x+1)) + 1/(12x²) − 1/(12(x+1)²). The derivative of f is −1/(6x³(x+1)³), strictly negative for x > 0, and f tends to zero at infinity. Thus f is strictly positive and q_N strictly decreases.")),
                    Paragraph(Text("Mathlib supplies the limit H_N − log N → γ. The two rational corrections tend to zero, so q_N also tends to γ. The comparison γ ≤ q_(N+1) < q_N preserves the strict gap and gives the stated inequality. This is a classical Euler–Maclaurin estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("euler-upper-at-128"),
                DeclarationHandle.Create(Prefix + "eulerMascheroni_upper_128"),
                H("A rational consequence at 128"),
                StatementSource.FromAuthor(Disp(Seq(
                    GammaLower, Sp, Lt, Sp, Seq(Frac, Grp(D(5, 7, 7, 2, 1, 5, 6, 6, 5, 0)), Grp(D(1, 0), Caret, Grp(D(1, 0))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Apply the preceding inequality at N = 128 and use log 128 = 7 log 2. The first twelve terms of the series for one half of log((1+t)/(1−t)), evaluated at t = 1/3, give a rational lower bound for log 2. Exact rational arithmetic then yields the displayed upper bound. This consequence depends on the uniform signed estimate."))),
                DescribeRole.Theorem))));

    private static Formula LowerFormula() => Disp(Seq(
        Forall, Sp, F.Id("N"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
        F.Id("N"), Sp, Ge, Sp, D(1), Sp, Implies, Sp,
        Seq(Frac, Grp(D(1)), Grp(D(2), F.Id("N"))), Sp, Minus, Sp,
        Seq(Frac, Grp(D(1)), Grp(D(1, 2), F.Id("N"), Caret, Grp(D(2)))), Sp, Lt, Sp,
        F.Id("H"), Underscore, F.Id("N"), Sp, Minus, Sp, Log, Sp, F.Id("N"),
        Sp, Minus, Sp, GammaLower));
}
