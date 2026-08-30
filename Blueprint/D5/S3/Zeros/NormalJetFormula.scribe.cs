using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class NormalJetFormulaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The conjugate Taylor channels determine every even normal jet and its first three values.",
        H("Normal Jet Formula"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normal-taylor-channel"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/NormalJetFormula.normalTaylorChannel"),
                H("Normal Taylor channel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a supplied real function, evaluation point, and complex direction, "
                        + "this formal power series has nth coefficient equal to the nth "
                        + "iterated derivative at that point times the nth directional phase "
                        + "divided by n factorial."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normal-intensity-series"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/NormalJetFormula.normalIntensitySeries"),
                H("Normal intensity series"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The formal normal intensity is constructed as the Cauchy product of the "
                        + "Taylor channels in directions minus i and plus i."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normal-jet"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/NormalJetFormula.normalJet"),
                H("Even normal coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At depth m, the normal jet is the real part of coefficient 2m in the "
                        + "constructed normal intensity series. It is not defined by the closed "
                        + "convolution formula proved below."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normal-jet-formula"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/NormalJetFormula.normal_jet_formula"),
                H("The normal jet convolution and its first three values"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real function Xi and every real point t, the public statement "
                            + "gives the signed factorial convolution of Xi's iterated derivatives "
                            + "at arbitrary depth, then states the depth zero, one, and two "
                            + "expansions and the half-second-derivative identity as four "
                            + "additional public conjuncts.")),
                    Paragraph(Text(
                        "The proof reads the coefficient of the Cauchy product of the two "
                            + "Taylor channels. The phase product is minus one to the power "
                            + "m+j, and two formal derivatives multiply coefficient two by two "
                            + "factorial. Thus the normal jet is constructed from channel "
                            + "semantics rather than defined to equal the target sum.")),
                    Paragraph(Text(
                        "Repository body-shape and name searches found no existing normal-jet "
                            + "owner. Pinned mathlib supplies PowerSeries.mk, coeff_mul, the "
                            + "antidiagonal-to-range identity, derivative, and coeff_derivative; "
                            + "the deposited theorem directly applies those primitives."))),
                DescribeRole.Theorem))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula TheoremFormula()
    {
        Formula xi = F.Id("Xi");
        Formula t = F.Id("t");
        Formula m = F.Id("m");
        Formula j = F.Id("j");
        Formula twoM = Seq(D(2), m);
        Formula reflectedIndex = Seq(twoM, Sp, Minus, Sp, j);
        Formula derivativeAtJ = Call("iteratedDeriv", j, xi, t);
        Formula derivativeAtReflectedIndex = Call(
            "iteratedDeriv", reflectedIndex, xi, t);
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
        Formula xiAtT = Call("Xi", t);
        Formula derivativeOne = Call("iteratedDeriv", D(1), xi, t);
        Formula derivativeTwo = Call("iteratedDeriv", D(2), xi, t);
        Formula derivativeThree = Call("iteratedDeriv", D(3), xi, t);
        Formula derivativeFour = Call("iteratedDeriv", D(4), xi, t);
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
        Formula twiceDifferentiated = Call(
            "derivative",
            Seq(Mathbb, Grp(F.Id("C"))),
            Call(
                "derivative",
                Seq(Mathbb, Grp(F.Id("C"))),
                Call("normalIntensitySeries", xi, t)));
        Formula secondNormalDerivative = new Formula.Fraction(
            Seq(Re, Grp(Call("coeff", D(0), twiceDifferentiated))),
            D(2));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, xi, Colon, Sp,
            Reals(), Sp, To, Sp, Reals(), Comma, Sp,
            t, Colon, Sp, Reals(), Comma,
            RowBreak, Grp(),
            Open, Forall, Sp, m, Colon, Sp, Naturals(), Comma, Sp,
            Call("normalJet", xi, t, m), Sp, Eq, Sp, convolution, Close, Sp, Land,
            RowBreak, Grp(),
            Call("normalJet", xi, t, D(0)), Sp, Eq, Sp,
            Power(xiAtT, D(2)), Sp, Land,
            RowBreak, Grp(),
            Call("normalJet", xi, t, D(1)), Sp, Eq, Sp,
            firstLaguerre, Sp, Land,
            RowBreak, Grp(),
            Call("normalJet", xi, t, D(2)), Sp, Eq, Sp,
            depthTwo, Sp, Land,
            RowBreak, Grp(),
            secondNormalDerivative, Sp, Eq, Sp, firstLaguerre, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
