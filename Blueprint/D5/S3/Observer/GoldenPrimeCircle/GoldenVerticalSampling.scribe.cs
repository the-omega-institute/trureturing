using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenPrimeCircle;

internal sealed class GoldenVerticalSamplingDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/GoldenPrimeCircle/GoldenVerticalSampling.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourier frequency on the golden scale circle equals vertical Mellin frequency on logarithmic scale.",
        H("Golden Vertical Sampling"),
        Blocks(
            Theorem("golden-angular-frequency-pos", "golden_angular_frequency_pos",
                "The Fundamental Golden Angular Frequency Is Positive", GoldenAngularFrequencyPosFormula(),
                "The fundamental frequency is pi divided by the positive logarithm of the golden ratio, so it is strictly positive.",
                "This fixes the sign of the frequency normalization and does not assert an Euler-product identity."),
            Theorem("golden-phase-vertical-frequency-identity", "golden_phase_vertical_frequency_identity",
                "Golden Fourier Phase Equals Vertical Mellin Phase", GoldenPhaseVerticalFrequencyIdentityFormula(),
                "For every real scale and integral mode, substituting the golden coordinate converts the Fourier phase into a logarithmic Mellin phase.",
                "The equality is finite algebra using the chosen normalizations; no positivity or analytic convergence hypothesis is introduced."),
            Theorem("golden-vertical-mode-spacing", "golden_vertical_mode_spacing",
                "Adjacent Modes Have Fundamental Golden Spacing", GoldenVerticalModeSpacingFormula(),
                "The vertical frequencies attached to consecutive integral modes differ by exactly one fundamental frequency.",
                "This is a spacing identity for the indexed frequencies and makes no claim about spectral values at those modes."),
            Theorem("golden-vertical-zero-mode", "golden_vertical_zero_mode",
                "The Zero Mode Has Zero Vertical Frequency", GoldenVerticalZeroModeFormula(),
                "Multiplying the fundamental frequency by the real zero gives the uncharged scale-average frequency.",
                "The statement identifies only the zero mode and does not characterize any nonzero Fourier coefficient."))));

    private static DocumentBlock.Describe Theorem(string id, string declaration,
        string heading, Formula formula, string firstParagraph, string secondParagraph) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(firstParagraph)), Paragraph(Text(secondParagraph))),
            DescribeRole.Theorem);

    private static Formula GoldenAngularFrequencyPosFormula() =>
        Statement([], Seq(D(0), Sp, Lt, Sp, F.Id("goldenAngularFrequency")));

    private static Formula GoldenPhaseVerticalFrequencyIdentityFormula()
    {
        Formula x = F.Id("x"); Formula k = F.Id("k"); Formula kReal = Coerce(k, Reals());
        return Statement([Typed(x, Reals()), Typed(k, Integers())],
            Seq(D(2), Sp, Times, Sp, Pi, Sp, Times, Sp, kReal,
                Sp, Times, Sp, Call("goldenScaleCoordinate", x), Sp, Eq, Sp,
                Grp(Seq(kReal, Sp, Times, Sp, F.Id("goldenAngularFrequency"))),
                Sp, Times, Sp, Call("log", x)));
    }

    private static Formula GoldenVerticalModeSpacingFormula()
    {
        Formula k = F.Id("k"); Formula frequency = F.Id("goldenAngularFrequency");
        Formula successorReal = Coerce(Seq(k, Sp, Plus, Sp, D(1)), Reals());
        Formula kReal = Coerce(k, Reals());
        return Statement([Typed(k, Integers())],
            Seq(Grp(Seq(successorReal, Sp, Times, Sp, frequency)), Sp, Minus, Sp,
                Grp(Seq(kReal, Sp, Times, Sp, frequency)), Sp, Eq, Sp, frequency));
    }

    private static Formula GoldenVerticalZeroModeFormula() =>
        Statement([], Seq(Coerce(D(0), Reals()), Sp, Times, Sp,
            F.Id("goldenAngularFrequency"), Sp, Eq, Sp, D(0)));

    private static Formula Statement(Formula[] binders, Formula conclusion)
    {
        List<Formula> items = [];
        if (binders.Length > 0)
        {
            items.Add(Forall); items.Add(Sp);
            for (int index = 0; index < binders.Length; index++)
            {
                if (index > 0) { items.Add(Comma); items.Add(Sp); }
                items.Add(binders[index]);
            }
            items.Add(Comma); items.Add(RowBreak); items.Add(Grp());
        }
        items.Add(Seq(Open, conclusion, Close)); items.Add(Dot);
        return Disp(Seq([.. items]));
    }

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula Coerce(Formula value, Formula type) => Seq(Open, value, Colon, Sp, type, Close);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
}
