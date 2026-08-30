using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class NormalJetFormulaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual completed-xi normal intensity determines every even Taylor coefficient.",
        H("Normal Jet Formula"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("critical-xi"),
                DeclarationHandle.Create("D5/S3/Zeros/NormalJetFormula.criticalXi"),
                H("Critical-line xi reading"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At a real ordinate t, this is the real part of the canonical completed-xi "
                        + "owner xiReading evaluated at one-half plus i times t. The imported "
                        + "conjugate-reflection theorem proves that this value is real."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normal-intensity"),
                DeclarationHandle.Create("D5/S3/Zeros/NormalJetFormula.normalIntensity"),
                H("Actual normal intensity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a real displacement delta and ordinate t, this is the complex norm "
                        + "squared of the canonical xiReading at one-half plus delta plus i times t. "
                        + "It is the source intensity itself, not a manufactured formal series."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normal-jet"),
                DeclarationHandle.Create("D5/S3/Zeros/NormalJetFormula.normalJet"),
                H("Even normal Taylor coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At depth m, the normal jet is the real iterated derivative of order 2m of "
                        + "the actual normal intensity at displacement zero, divided by 2m "
                        + "factorial. It is not defined by the convolution formula below."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normal-jet-formula"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/NormalJetFormula.normal_jet_formula"),
                H("The completed-xi normal jet formula"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real ordinate, the first public conjunct gives every even "
                            + "Taylor coefficient of the actual completed-xi intensity as the "
                            + "signed factorial convolution of critical-line derivatives. Four "
                            + "further public conjuncts state the depth zero, one, and two cases "
                            + "and one half of the actual second displacement derivative.")),
                    Paragraph(Text(
                        "The proof uses the frozen differentiability of xiReading and its frozen "
                            + "conjugate-reflection identity. A private entire extension identifies "
                            + "the product of the two affine critical-line channels with the real "
                            + "norm-squared intensity before the iterated product rule is applied.")),
                    Paragraph(Text(
                        "Pinned mathlib supplies the iterated Leibniz rule, affine derivative laws, "
                            + "and the real-to-complex derivative bridges. No analyticity premise is "
                            + "added to the theorem because the canonical xiReading owner already "
                            + "proves global complex differentiability."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Zeros/CompletedZeta")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Zeros/Symmetry/ZetaConjugationCovariance")),
        ]));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula TheoremFormula()
    {
        Formula t = F.Id("t");
        Formula m = F.Id("m");
        Formula j = F.Id("j");
        Formula delta = F.Id("delta");
        Formula criticalXi = F.Id("criticalXi");
        Formula twoM = Seq(D(2), m);
        Formula reflectedIndex = Seq(twoM, Sp, Minus, Sp, j);
        Formula derivativeAtJ = Call("iteratedDeriv", j, criticalXi, t);
        Formula derivativeAtReflectedIndex = Call(
            "iteratedDeriv", reflectedIndex, criticalXi, t);
        Formula sign = Power(
            Seq(Open, Minus, D(1), Close),
            Seq(m, Sp, Plus, Sp, j));
        Formula denominator = Seq(
            Call("factorial", j), Sp, Cdot, Sp,
            Call("factorial", reflectedIndex));
        Formula summand = Seq(
            new Formula.Fraction(sign, denominator), Sp, Cdot, Sp,
            derivativeAtJ, Sp, Cdot, Sp, derivativeAtReflectedIndex);
        Formula convolution = Seq(
            Sum, Underscore, Grp(Seq(j, Eq, D(0))),
            Caret, Grp(twoM), Sp, summand);
        Formula xiAtT = Call("criticalXi", t);
        Formula derivativeOne = Call("iteratedDeriv", D(1), criticalXi, t);
        Formula derivativeTwo = Call("iteratedDeriv", D(2), criticalXi, t);
        Formula derivativeThree = Call("iteratedDeriv", D(3), criticalXi, t);
        Formula derivativeFour = Call("iteratedDeriv", D(4), criticalXi, t);
        Formula firstLaguerre = Seq(
            Power(derivativeOne, D(2)), Sp, Minus, Sp,
            xiAtT, Sp, Cdot, Sp, derivativeTwo);
        Formula depthTwo = Seq(
            new Formula.Fraction(D(1), D(4)), Sp, Cdot, Sp,
            Power(derivativeTwo, D(2)), Sp, Minus, Sp,
            new Formula.Fraction(D(1), D(3)), Sp, Cdot, Sp,
            derivativeOne, Sp, Cdot, Sp, derivativeThree, Sp, Plus, Sp,
            new Formula.Fraction(D(1), D(1, 2)), Sp, Cdot, Sp,
            xiAtT, Sp, Cdot, Sp, derivativeFour);
        Formula intensityAsFunction = Seq(
            Open, delta, Sp, Mapsto, Sp, Call("normalIntensity", delta, t), Close);
        Formula secondNormalDerivative = new Formula.Fraction(
            Call("iteratedDeriv", D(2), intensityAsFunction, D(0)), D(2));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, t, Colon, Sp, Reals(), Comma,
            RowBreak, Grp(),
            Open, Forall, Sp, m, Colon, Sp, Naturals(), Comma, Sp,
            Call("normalJet", t, m), Sp, Eq, Sp, convolution, Close, Sp, Land,
            RowBreak, Grp(),
            Call("normalJet", t, D(0)), Sp, Eq, Sp,
            Power(xiAtT, D(2)), Sp, Land,
            RowBreak, Grp(),
            Call("normalJet", t, D(1)), Sp, Eq, Sp,
            firstLaguerre, Sp, Land,
            RowBreak, Grp(),
            Call("normalJet", t, D(2)), Sp, Eq, Sp,
            depthTwo, Sp, Land,
            RowBreak, Grp(),
            secondNormalDerivative, Sp, Eq, Sp, firstLaguerre, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
