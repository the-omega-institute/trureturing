using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma;

internal sealed class RenormalizedWeilMultiplierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula zeros = F.Id("Z");
        Formula test = F.Id("f");
        Formula scale = F.Id("L");
        Formula xi = Xi;
        Formula u = F.Id("u");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula convolution = Call("convolutionSquare", test);
        Formula supportInterval = Seq(
            OpenBracket, Minus, scale, Comma, Sp, scale, CloseBracket);
        Formula bInf = new Formula.Subscript(F.Id("b"), Infty);
        Formula rL = new Formula.Subscript(F.Id("r"), scale);
        Formula quarter = new Formula.Fraction(D(1), D(4));
        Formula digammaArgument = Seq(
            quarter, Sp, Plus, Sp,
            new Formula.Fraction(Seq(F.Id("i"), Sp, xi), D(2)));
        Formula bInfValue = Seq(
            Re, Open, Psi, Open, digammaArgument, Close, Close,
            Sp, Minus, Sp, Call("log", Pi), Sp, Plus, Sp,
            new Formula.Fraction(
                D(1),
                Seq(xi, Caret, Grp(D(2)), Sp, Plus, Sp, quarter)));
        Formula primeCutoff = Call("exp", Seq(D(2), scale));
        Formula continuousTransform = Seq(
            Int, Underscore, Grp(reals), Sp,
            Call("EL", Seq(D(2), scale), u), Sp,
            Re, Open, Call("exp", Seq(Minus, F.Id("i"), Sp, xi, Sp, u)), Close,
            Sp, F.Id("d"), u);
        Formula rLValue = Seq(
            Minus, D(2), Pi, Sp, Call("PX", primeCutoff, xi), Sp,
            Minus, Sp, continuousTransform);
        Formula zeroSide = Call("zeroSum", zeros, convolution, F.Id("hZero"));
        Formula transformEnergy = Seq(
            Lvert, Call("fourierLaplace", test, xi), Rvert, Caret, Grp(D(2)));
        Formula multiplierForm = Seq(
            new Formula.Fraction(D(1), Seq(D(2), Pi)), Sp,
            Int, Underscore, Grp(reals), Sp,
            Open, bInf, Open, xi, Close, Sp, Minus, Sp,
            rL, Open, xi, Close, Close, Sp,
            transformEnergy, Sp, F.Id("d"), xi);

        Formula statement = Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, zeros, Colon, Sp,
                Operatorname, Grp(F.Id("ZeroData")), Comma, Sp,
                test, InMacro, Sp, Mathcal, Grp(F.Id("W")), Comma, Sp,
                scale, InMacro, Sp, reals, Comma),
            Seq(
                F.Id("hL"), Colon, Sp, D(0), Sp, Lt, Sp, scale, Comma, Sp,
                F.Id("hSupport"), Colon, Sp, Call("tsupport", test), Sp,
                Subseteq, Sp, supportInterval, Comma),
            Seq(
                F.Id("hZero"), Colon, Sp,
                Call("SymmetricConvergent", zeros, convolution), Comma, Sp,
                F.Id("hArch"), Colon, Sp,
                Call("ArchimedeanConvergent", convolution), Sp, Rightarrow),
            Seq(
                Operatorname, Grp(F.Id("let")), Sp,
                bInf, Open, xi, Close, Sp, Eq, Sp, bInfValue, Comma),
            Seq(
                rL, Open, xi, Close, Sp, Eq, Sp, rLValue, Comma),
            Seq(zeroSide, Sp, Eq, Sp, multiplierForm, Dot),
        ]));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The classical zero-side Weil form is the Fourier multiplier form obtained by "
                + "subtracting the finite prime-continuum discrepancy from the shifted "
                + "Archimedean baseline.",
            H("Renormalized Weil Multiplier"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("renormalized-weil-multiplier"),
                    DeclarationHandle.Create(
                        "D5/S3/Weil/ZetaGamma/RenormalizedWeilMultiplier."
                            + "renormalized_weil_multiplier"),
                    H("The completed Weil form is a single discrepancy multiplier"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "W is the canonical carrier of even smooth compactly supported "
                                + "complex tests. The positive scale and support premise place "
                                + "the convolution square in the explicit-formula window, while "
                                + "hZero and hArch supply its two convergence witnesses.")),
                        Paragraph(Text(
                            "The displayed b-infinity is constructed from the unshifted digamma "
                                + "and the Green resolvent term; r-L uses the canonical finite "
                                + "prime multiplier PX and continuous reference density EL. The "
                                + "digamma recurrence identifies this baseline with the shifted "
                                + "chart and yields the single multiplier."))),
                    DescribeRole.Theorem))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
