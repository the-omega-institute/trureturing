using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class HarmonicScoreLocalAverageDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local averaging gives a three-band lower bound for a finite weighted sine score.",
        H("Local averaging of a finite harmonic score"),
        Blocks(
            Paragraph(Text(
                "Fix a finite set s of indices in a type J. Each j in s has a real angular "
                + "frequency γⱼ and a real weight wⱼ. For a real cutoff Z, sum over the "
                + "indices with γⱼ ≤ Z. The notation W and S suppresses the common set, "
                + "frequencies and weights.")),
            Describe.Lean(
                DescribeId.Create("cutoff-mass"),
                DeclarationHandle.Create("D5/S3/Fourier/HarmonicScoreLocalAverage.cutoffMass"),
                H("Mass through the cutoff"),
                StatementSource.FromAuthor(Disp(Equal(W(F.Id("Z")),
                    Seq(Summation(F.Id("j")), Weight(F.Id("j")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The cutoff includes frequencies equal to Z. An empty cutoff has mass zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cutoff-score"),
                DeclarationHandle.Create("D5/S3/Fourier/HarmonicScoreLocalAverage.cutoffScore"),
                H("Sine score through the cutoff"),
                StatementSource.FromAuthor(Disp(Equal(S(F.Id("Z"), F.Id("v")),
                    Seq(Summation(F.Id("j")), Weight(F.Id("j")),
                        Call("sin", Seq(Frequency(F.Id("j")), F.Id("v"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The argument v is the time in the score. The estimates evaluate the score "
                    + "at v = u/r as u runs through the window."))),
                DescribeRole.Definition),
            Paragraph(Text(
                "For the following estimates assume γⱼ > 0 and wⱼ ≥ 0 for every j in s. "
                + "Take real cutoffs 0 < X ≤ Y ≤ T, a scale r > 0, a window length h > 0, "
                + "and any real left endpoint b.")),
            Describe.Lean(
                DescribeId.Create("three-band-average"),
                DeclarationHandle.Create(
                    "D5/S3/Fourier/HarmonicScoreLocalAverage.cutoffScore_average_lower"),
                H("Lower bound for the window mean"),
                StatementSource.FromAuthor(Disp(Seq(LowerBound(), Le, Mean()))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For γⱼ ≤ X, sine is one-Lipschitz and the argument moves by at most "
                        + "hX/r from its left-endpoint value. For X < γⱼ ≤ Y, the mean of each "
                        + "sine is at least −1. For Y < γⱼ ≤ T, integrating the sine at "
                        + "angular frequency γⱼ/r gives the difference of the endpoint "
                        + "cosines multiplied by r/γⱼ. After division by h the result is "
                        + "at least −2r/(hγⱼ), hence at least −2r/(hY). Nonnegative weights "
                        + "preserve each inequality. The two band masses are the respective "
                        + "differences of cumulative masses.")),
                    Paragraph(Text(
                        "The endpoint estimate is the real sine version of the normalized "
                        + "finite character average in norm_avg_le, "
                        + "ExpSumCoeffEqZeroOfVanishing.lean, lines 32–62, from the "
                        + "Riemann hypothesis repository at b8864ecd5798c6030a03d756fab95f0b89a12754. "
                        + "Its frequencies are measured in cycles per unit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("same-window-point"),
                DeclarationHandle.Create(
                    "D5/S3/Fourier/HarmonicScoreLocalAverage.exists_cutoffScore_ge"),
                H("A score at least the bound in the same window"),
                StatementSource.FromAuthor(Disp(Seq(Exists, Sp, F.Id("u"), InMacro,
                    OpenBracket, F.Id("b"), Comma, Add(F.Id("b"), F.Id("h")), CloseBracket,
                    Comma, Quad, Sp, LowerBound(), Le, Sp, S(F.Id("T"), Div(F.Id("u"), F.Id("r")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite score is continuous. The first integral mean value theorem "
                    + "with weight one gives a point in the closed window where the score "
                    + "equals its window mean."))),
                DescribeRole.Theorem))));

    private static Formula Subscript(Formula basis, Formula index) =>
        Seq(basis, Underscore, Grp(index));

    private static Formula Weight(Formula j) => Subscript(F.Id("w"), j);
    private static Formula Frequency(Formula j) => Subscript(GammaLower, j);

    private static Formula Summation(Formula j) =>
        Seq(Subscript(Sum, Seq(j, InMacro, Sp, F.Id("s"), Comma,
            Frequency(j), Le, Sp, F.Id("Z"))), Thin);

    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula W(Formula z) => Subscript(F.Id("W"), z);
    private static Formula S(Formula z, Formula v) => Seq(Subscript(F.Id("S"), z), Open, v, Close);

    private static Formula LowerBound()
    {
        var x = F.Id("X");
        var y = F.Id("Y");
        var t = F.Id("T");
        var h = F.Id("h");
        var r = F.Id("r");
        return Seq(S(x, Div(F.Id("b"), r)), Minus, Div(Seq(h, x), r), W(x),
            Minus, Open, Subtract(W(y), W(x)), Close,
            Minus, Div(Seq(D(2), r), Seq(h, y)), Open, Subtract(W(t), W(y)), Close);
    }

    private static Formula Mean()
    {
        var b = F.Id("b");
        var h = F.Id("h");
        var u = F.Id("u");
        return Seq(Div(D(1), h), Int, Underscore, Grp(b), Caret, Grp(Add(b, h)),
            Sp, S(F.Id("T"), Div(u, F.Id("r"))), Thin, F.Id("d"), u);
    }
}
