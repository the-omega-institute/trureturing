using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class FixedScaleWeilQuadraticFormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula zeros = F.Id("Z");
        Formula test = F.Id("f");
        Formula scale = F.Id("L");
        Formula variable = F.Id("x");
        Formula frequency = Xi;
        Formula convolutionSquare = Seq(
            Operatorname, Grp(F.Id("convolutionSquare")), Open, test, Close);
        Formula zeroSide = Seq(
            Operatorname, Grp(F.Id("zeroSum")), Open,
            zeros, Comma, Sp, convolutionSquare, Comma, Sp, F.Id("hZero"), Close);
        Formula poleReadout = Seq(
            Int, Underscore, Grp(Mathbb, Grp(F.Id("R"))), Sp,
            Operatorname, Grp(F.Id("cosh")), Open, Frac, Grp(variable), Grp(D(2)), Close,
            Sp, test, Open, variable, Close, Sp, F.Id("d"), variable);
        Formula transformEnergy = Seq(
            Lvert, Operatorname, Grp(F.Id("fourierLaplace")), Open,
            test, Comma, Sp, frequency, Close, Rvert, Caret, Grp(D(2)));
        Formula multiplierIntegral = Seq(
            Frac, Grp(D(1)), Grp(D(2), Pi), Sp,
            Int, Underscore, Grp(Mathbb, Grp(F.Id("R"))), Sp,
            Operatorname, Grp(F.Id("fixedScaleMultiplier")), Open,
            scale, Comma, Sp, frequency, Close, Sp,
            transformEnergy, Sp, F.Id("d"), frequency);
        Formula rightSide = Seq(
            D(2), Sp, Lvert, poleReadout, Rvert, Caret, Grp(D(2)), Sp,
            Plus, Sp, multiplierIntegral);
        Formula supportInterval = Seq(
            OpenBracket, Minus, scale, Comma, Sp, scale, CloseBracket);

        return DocumentDefinition.Create(ScribeNode.Create(
            "The fixed-scale Weil zero-side form is the completed Fourier multiplier form "
                + "plus its rank-one pole energy, with an equivalent positivity test.",
            H("Fixed-Scale Weil Quadratic Form"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("fixed-scale-weil-form-and-positivity-test"),
                    DeclarationHandle.Create(
                        "D5/S3/Weil/ZetaBridge/FixedScaleWeilQuadraticForm."
                            + "fixed_scale_weil_quadratic_form"),
                    H("The fixed-scale Weil form and its positivity test"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, zeros, Colon, Sp,
                        Operatorname, Grp(F.Id("ZeroData")), Comma, Sp,
                        test, InMacro, Sp, Mathcal, Grp(F.Id("W")), Comma, Sp,
                        scale, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                        F.Id("hSupport"), Colon, Sp,
                        Operatorname, Grp(F.Id("tsupport")), Open, test, Close,
                        Sp, Subseteq, Sp, supportInterval, Comma, Sp,
                        F.Id("hZero"), Colon, Sp,
                        Operatorname, Grp(F.Id("SymmetricConvergent")), Open,
                        zeros, Comma, Sp, convolutionSquare, Close, Comma, Sp,
                        F.Id("hArch"), Colon, Sp,
                        Operatorname, Grp(F.Id("ArchimedeanConvergent")), Open,
                        convolutionSquare, Close, Sp, Rightarrow, Sp,
                        Grp(zeroSide, Sp, Eq, Sp, rightSide), Sp, Land, Sp,
                        Grp(D(0), Sp, Leq, Sp, Re, Open, zeroSide, Close,
                            Sp, Leftrightarrow, Sp,
                            D(0), Sp, Leq, Sp, Re, Open, rightSide, Close)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Here W is the frozen carrier of even smooth compactly supported complex "
                            + "test functions. The supplied support proof places f in the fixed "
                            + "scale interval; hZero and hArch are exactly the convergence witnesses "
                            + "used by zeroSum and the frozen explicit formula. The multiplier is "
                            + "defined as two pi times the sum of the canonical Archimedean mu and "
                            + "finite prime-power PX multipliers at exp(2L). The first public conjunct "
                            + "is the exact complex identity, and its real part gives the second "
                            + "public positivity equivalence."))),
                    DescribeRole.Theorem))));
    }
}
