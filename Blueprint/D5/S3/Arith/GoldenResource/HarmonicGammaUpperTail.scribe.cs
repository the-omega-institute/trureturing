using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class HarmonicGammaUpperTailDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/HarmonicGammaUpperTail.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/nist2026asymptotic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The corrected harmonic-logarithmic remainder lies strictly between zero and its fourth-order term.",
        H("A Fourth-Order Harmonic–Logarithmic Tail Bound"),
        Blocks(
            Paragraph(Text("For a positive integer N, write H_N for the harmonic sum and γ for the Euler–Mascheroni constant. Set R_N = H_N − log N − γ − 1/(2N) + 1/(12N²).")),
            Describe.Lean(
                DescribeId.Create("harmonic-log-tail-upper"),
                DeclarationHandle.Create(Prefix + "harmonic_log_tail_upper"),
                H("The strict fourth-order upper estimate"),
                StatementSource.FromAuthor(BoundFormula(false)),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Let q_N = H_N − log N − 1/(2N) + 1/(12N²), and let c(x) = 1/(120x⁴). The consecutive difference q_N − q_(N+1) is f(N), where f(x) = log(x+1) − log x − 1/(2x) − 1/(2(x+1)) + 1/(12x²) − 1/(12(x+1)²). Put w(x) = c(x) − c(x+1).")),
                    Paragraph(Text("For x > 0, f′(x) = −1/(6x³(x+1)³) and (f−w)′(x) = (5x²+5x+1)/(30x⁵(x+1)⁵) > 0. Both f and f−w tend to zero at infinity. Thus f(x) < w(x), and a_N = q_N − c(N) satisfies a_N < a_(N+1).")),
                    Paragraph(Text("Mathlib supplies the finite telescoping identity: the sum of a_(N+k+1) − a_(N+k) for 0 ≤ k < m equals a_(N+m) − a_N. Every summand is positive, so a_N ≤ a_(N+m). The known limit q_N → γ and c(N) → 0 give a_(N+1) ≤ γ. Keeping the first strict step yields a_N < a_(N+1) ≤ γ, which is precisely R_N < 1/(120N⁴). This is the positive-real Euler–Maclaurin remainder estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("harmonic-log-tail-bounds"),
                DeclarationHandle.Create(Prefix + "harmonic_log_tail_bounds"),
                H("The two-sided strict bracket"),
                StatementSource.FromAuthor(BoundFormula(true)),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The signed lower estimate gives R_N > 0. Combining it with the preceding upper estimate produces the full strict bracket for every positive integer N."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("euler-lower-at-64"),
                DeclarationHandle.Create(Prefix + "eulerMascheroni_lower_64"),
                H("A rational consequence at 64"),
                StatementSource.FromAuthor(Disp(Seq(
                    Seq(Frac, Grp(D(5, 7, 7, 2, 1, 5, 6, 6, 4, 9)), Grp(D(1, 0), Caret, Grp(D(1, 0)))),
                    Sp, Lt, Sp, GammaLower))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Apply the fourth-order estimate at N = 64 and write log 64 = 6 log 2. The first fourteen terms of the series for one half of log((1+t)/(1−t)), evaluated at t = 1/3, together with its absolute remainder bound, give a rational upper bound for log 2. Exact rational arithmetic yields the displayed lower bound for γ. Its proof depends on the uniform upper tail estimate."))),
                DescribeRole.Theorem))));

    private static Formula Remainder() => Seq(
        F.Id("H"), Underscore, F.Id("N"), Sp, Minus, Sp, Log, Sp, F.Id("N"),
        Sp, Minus, Sp, GammaLower, Sp, Minus, Sp,
        Seq(Frac, Grp(D(1)), Grp(D(2), F.Id("N"))), Sp, Plus, Sp,
        Seq(Frac, Grp(D(1)), Grp(D(1, 2), F.Id("N"), Caret, Grp(D(2)))));

    private static Formula BoundFormula(bool twoSided) => Disp(Seq(
        Forall, Sp, F.Id("N"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
        F.Id("N"), Sp, Ge, Sp, D(1), Sp, Implies, Sp,
        twoSided ? Seq(D(0), Sp, Lt, Sp, Remainder()) : Remainder(), Sp, Lt, Sp,
        Seq(Frac, Grp(D(1)), Grp(D(1, 2, 0), F.Id("N"), Caret, Grp(D(4))))));
}
