using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma;

internal sealed class PoleContinuumCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula test = F.Id("f");
        Formula u = F.Id("u");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula xi = F.Id("xi");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula convolution = Call("convolutionSquare", test);
        Formula convolutionAtU = Call("convolutionSquare", test, u);
        Formula continuousMain = Seq(
            Int, Underscore, Grp(D(0)), Caret, Grp(Infty), Sp,
            Call("exp", new Formula.Fraction(u, D(2))), Sp,
            Open, convolutionAtU, Sp, Plus, Sp,
            Call("convolutionSquare", test, Seq(Minus, u)), Close, Sp,
            F.Id("d"), u);
        Formula greenKernel = Call(
            "exp",
            Seq(Minus, new Formula.Fraction(new Formula.Absolute(Seq(x, Minus, y)), D(2))));
        Formula greenForm = Seq(
            Int, Underscore, Grp(reals), Sp,
            Int, Underscore, Grp(reals), Sp,
            greenKernel, Sp, Call("f", x), Sp,
            Overline, Grp(Call("f", y)), Sp,
            F.Id("d"), y, Sp, F.Id("d"), x);
        Formula poleContinuum = Disp(Seq(
            Forall, Sp, test, InMacro, Sp, Mathcal, Grp(F.Id("W")), Comma, Sp,
            Call("poleTerm", convolution), Sp, Minus, Sp, continuousMain,
            Sp, Eq, Sp, greenForm));

        Formula quarter = new Formula.Fraction(D(1), D(4));
        Formula fiveQuarters = new Formula.Fraction(D(5), D(4));
        Formula imaginaryFrequency = new Formula.Fraction(Seq(F.Id("i"), Sp, xi), D(2));
        Formula baseArgument = Seq(quarter, Sp, Plus, Sp, imaginaryFrequency);
        Formula shiftedArgument = Seq(fiveQuarters, Sp, Plus, Sp, imaginaryFrequency);
        Formula bInf = new Formula.Subscript(F.Id("b"), Infty);
        Formula greenMultiplier = new Formula.Fraction(
            D(1),
            Seq(new Formula.Power(xi, D(2)), Sp, Plus, Sp, quarter));
        Formula archimedeanShift = Disp(new Formula.Aligned([
            Seq(Forall, Sp, xi, InMacro, Sp, reals, Comma),
            Seq(
                Operatorname, Grp(F.Id("let")), Sp, bInf, Sp, Eq, Sp,
                Re, Open, Psi, Open, baseArgument, Close, Close,
                Sp, Minus, Sp, Call("log", Pi), Sp, Plus, Sp, greenMultiplier,
                Comma),
            Seq(
                bInf, Sp, Eq, Sp,
                Re, Open, Psi, Open, shiftedArgument, Close, Close,
                Sp, Minus, Sp, Call("log", Pi)),
        ]));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The completed-zeta pole pair minus the continuous prime density is the decaying "
                + "Green-kernel form, and its multiplier advances the digamma argument by one.",
            H("Pole-Continuum Completion"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("pole-continuum-completion"),
                    DeclarationHandle.Create(
                        "D5/S3/Weil/ZetaGamma/PoleContinuumCompletion."
                            + "pole_continuum_completion"),
                    H("The pole-continuum difference is the decaying Green form"),
                    StatementSource.FromAuthor(poleContinuum),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "W is the canonical carrier of even smooth compactly supported "
                                + "complex tests. The displayed half-line integral is the "
                                + "continuous prime main density evaluated on the canonical "
                                + "convolution square.")),
                        Paragraph(Text(
                            "Splitting the two pole evaluations into growing and decaying "
                                + "exponentials cancels the growing half-line contribution. "
                                + "Fubini and translation invariance identify the remainder "
                                + "with the displayed full-line Green kernel."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("archimedean-shift-completion"),
                    DeclarationHandle.Create(
                        "D5/S3/Weil/ZetaGamma/PoleContinuumCompletion."
                            + "archimedean_shift_completion"),
                    H("The Green multiplier advances the digamma argument by one"),
                    StatementSource.FromAuthor(archimedeanShift),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The identity is the exact digamma recurrence at one quarter plus "
                            + "half the imaginary frequency. Taking real parts turns the "
                            + "reciprocal term into the displayed Green multiplier."))),
                    DescribeRole.Theorem))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
