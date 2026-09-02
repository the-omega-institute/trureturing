using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class WhiteSpectrumDeltaNormalizationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/TestFunctions/WhiteSpectrumDeltaNormalization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Angular-frequency normalization turns white Lebesgue spectrum into ordinary "
            + "Lebesgue measure, whose inverse Fourier transform is the Dirac distribution.",
        H("White Spectrum Delta Normalization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("angular-frequency-pushforward"),
                Handle("angularFrequencyPushforward"),
                H("Angular frequency pushforward"),
                StatementSource.FromAuthor(AngularPushforwardFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The coordinate xi divided by two pi converts the repository's angular "
                        + "frequency to Mathlib's standard Fourier frequency."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normalized-white-frequency-pushforward"),
                Handle("normalized_white_frequency_pushforward"),
                H("Normalized white spectrum becomes Lebesgue measure"),
                StatementSource.FromAuthor(PushforwardIdentityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Jacobian of xi mapped to xi divided by two pi cancels the source "
                        + "density one over two pi exactly."))),
                DescribeRole.Proposition),
            Describe.Lean(
                DescribeId.Create("inverse-angular-fourier"),
                Handle("inverseAngularFourier"),
                H("Inverse angular Fourier transform"),
                StatementSource.FromAuthor(InverseAngularFourierFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a measure whose pushed-forward form has temperate growth, the "
                        + "angular inverse transform is Mathlib's distributional inverse "
                        + "Fourier transform after the frequency-coordinate change."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normalized-white-spectrum-inverse-fourier"),
                Handle("normalized_white_spectrum_inverse_fourier"),
                H("Normalized white spectrum transforms to Dirac mass"),
                StatementSource.FromAuthor(MainTheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The normalized angular white spectrum pushes forward to ordinary "
                            + "Lebesgue measure. Mathlib's tempered-distribution Fourier "
                            + "pair then identifies its inverse transform with delta at zero.")),
                    Paragraph(Text(
                        "No Weil source, local completion, resolvent estimate, or Riemann "
                            + "hypothesis input is used in this normalization identity."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string declaration) =>
        DeclarationHandle.Create(Prefix + declaration);

    private static Formula AngularPushforwardFormula() => Disp(Seq(
        Forall, Sp, Nu, Sp, InMacro, Sp, MeasureType(), Comma, Sp,
        Pushforward(Nu), Sp, Eq, Sp,
        Call("map", F.Id("mathlibFrequency"), Nu), Dot));

    private static Formula PushforwardIdentityFormula() => Disp(Seq(
        Pushforward(White()), Sp, Eq, Sp, Call("volume", RealType()), Dot));

    private static Formula InverseAngularFourierFormula() => Disp(Seq(
        Forall, Sp, Nu, Sp, InMacro, Sp, MeasureType(), Comma, Sp,
        Call("inverseAngularFourier", Nu), Sp, Eq, Sp,
        Call("fourierInv", Call("toTemperedDistribution", Pushforward(Nu))), Dot));

    private static Formula MainTheoremFormula() => Disp(Seq(
        Call("inverseAngularFourier", White()), Sp, Eq, Sp,
        DeltaLower, Underscore, Grp(D(0)), Dot));

    private static Formula Pushforward(Formula measure) =>
        Call("angularFrequencyPushforward", measure);

    private static Formula White() => Seq(F.Id("m"), Underscore, Grp(D(0)));

    private static Formula MeasureType() => Call("Measure", RealType());

    private static Formula RealType() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
