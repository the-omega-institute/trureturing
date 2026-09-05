using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GermWindow;

internal sealed class GermJetModeLemmaDocument
    : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Analytic/GermWindow/GermJetModeLemma.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reusable certified-numerics infrastructure for one mode of the golden germ: "
            + "rational beta, logarithm, exponential, phase, and trigonometric data are "
            + "propagated to coordinate enclosures for a term and its derivative.",
        H("Generic Golden Germ Mode Enclosures"),
        Blocks(
            Paragraph(Text(
                "This module is the hand-written L2c infrastructure layer. It introduces "
                    + "no carrier definition. Its literal rational hypotheses certify the golden "
                    + "beta interval, a seventy-bit logarithm interval, an order-20 exponential "
                    + "envelope, exact pi phase reduction, order-10 sine and cosine envelopes, "
                    + "and the final interval arithmetic. The module is reusable "
                    + "certified-numerics infrastructure and makes no claim about RH.")),
            Entry(
                "seventy-bit-logarithm-enclosure",
                "log_two_binary_70",
                LogTwoFormula(),
                "The binary series encloses log 2 to seventy bits",
                "Mathlib's logarithm-series remainder bound is normalized to the displayed "
                    + "rational center and an error of 2^{-70}.",
                DescribeRole.Theorem),
            Entry(
                "generic-mode-term-enclosure",
                "mode_term_enclosure",
                ModeTermFormula(),
                "Rational mode data encloses one complex germ term",
                "For every mode v at most sixty, the displayed decidable rational hypotheses "
                    + "produce real and imaginary endpoint bounds for 2^{-c beta(v)}. Both "
                    + "returned interval widths are at most 10^{-15}. The live escape step "
                    + "multiplies the certified exponential enclosure by the phase-reduced "
                    + "cosine and sine enclosures and propagates the two error terms.",
                DescribeRole.Theorem),
            Entry(
                "generic-mode-derivative-enclosure",
                "mode_deriv_enclosure",
                ModeDerivativeFormula(),
                "Rational mode data encloses the matching derivative term",
                "The derivative certificate reuses the certified term coordinates and "
                    + "encloses the rational amplitude beta(v) log 2. Product-error "
                    + "propagation then bounds both coordinates of -beta(v) log(2) "
                    + "2^{-c beta(v)}, again with widths at most 10^{-15}.",
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/GermWindow/GermZeroCertificateReduction")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Certified/TrigEnvelopePhaseReduction")),
        ]));

    private static DocumentBlock.Describe Entry(
        string id,
        string declaration,
        Formula statement,
        string title,
        string prose,
        DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Module + declaration),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))),
            role);

    private static Formula LogTwoFormula()
    {
        Formula numerator = F.D(
            8, 1, 0, 2, 6, 2, 0, 4, 9, 4, 6, 9, 1, 4, 2, 7, 2, 6, 1, 8,
            3, 4, 6, 6, 0, 9, 0, 8, 2, 1, 0, 2, 2, 5, 0, 8, 0, 1, 1, 1, 4,
            9, 0, 7, 7, 2, 9);
        Formula denominator = F.D(
            1, 1, 6, 8, 9, 6, 1, 0, 4, 0, 5, 8, 9, 6, 6, 0, 1, 5, 6, 4,
            6, 7, 5, 0, 9, 4, 7, 5, 5, 4, 9, 7, 8, 3, 1, 4, 9, 8, 7, 9,
            9, 2, 2, 5, 2, 4, 1, 6);
        Formula approximation = Fraction(numerator, denominator);
        Formula error = Fraction(F.D(1), Power(F.Seq(F.D(2)), F.D(7, 0)));
        return Disp(LessOrEqual(
            Absolute(Subtract(Call("log", F.D(2)), approximation)),
            error));
    }

    private static Formula ModeTermFormula()
    {
        Formula v = F.Id("v"), scale = F.Id("scale"), swap = F.Id("swap");
        Formula betaLo = F.Id("betaLo"), betaHi = F.Id("betaHi");
        Formula xLo = F.Id("xLo"), xHi = F.Id("xHi");
        Formula thetaLo = F.Id("thetaLo"), thetaHi = F.Id("thetaHi");
        Formula phaseLo = F.Id("phaseLo"), phaseHi = F.Id("phaseHi");
        Formula r0 = F.Id("r0"), rDelta = F.Id("rDelta"), piErr = F.Id("piErr");
        Formula qLo = F.Id("qLo"), qHi = F.Id("qHi");
        Formula baseLo = F.Id("baseLo"), baseHi = F.Id("baseHi");
        Formula expLo = F.Id("expLo"), expHi = F.Id("expHi");
        Formula exp0 = F.Id("exp0"), expErr = F.Id("expErr");
        Formula cos0 = F.Id("cos0"), sin0 = F.Id("sin0");
        Formula cosBaseErr = F.Id("cosBaseErr"), sinBaseErr = F.Id("sinBaseErr");
        Formula cosErr = F.Id("cosErr"), sinErr = F.Id("sinErr");
        Formula thetaCos0 = F.Id("thetaCos0"), thetaSin0 = F.Id("thetaSin0");
        Formula thetaCosErr = F.Id("thetaCosErr"), thetaSinErr = F.Id("thetaSinErr");
        Formula reLo = F.Id("termReLo"), reHi = F.Id("termReHi");
        Formula imLo = F.Id("termImLo"), imHi = F.Id("termImHi");
        Formula phaseIndex = Call("phaseIndexPi", phaseLo);
        Formula sign = Power(ParenthesizedNegative(F.D(1)), phaseIndex);
        Formula expTaylorLo = Subtract(
            SumRange(F.D(2, 0), Fraction(Power(qLo, F.Id("i")), Factorial(F.Id("i")))),
            Fraction(Multiply(Power(Absolute(qLo), F.D(2, 0)), F.D(2, 1)),
                Multiply(Factorial(F.D(2, 0)), F.D(2, 0))));
        Formula expTaylorHi = Add(
            SumRange(F.D(2, 0), Fraction(Power(qHi, F.Id("i")), Factorial(F.Id("i")))),
            Fraction(Multiply(Power(Absolute(qHi), F.D(2, 0)), F.D(2, 1)),
                Multiply(Factorial(F.D(2, 0)), F.D(2, 0))));
        Formula cosTaylor = SumRange(F.D(1, 0),
            Fraction(
                Multiply(Power(ParenthesizedNegative(F.D(1)), F.Id("i")),
                    Power(r0, Multiply(F.D(2), F.Id("i")))),
                Factorial(Multiply(F.D(2), F.Id("i")))));
        Formula sinDegree = Add(Multiply(F.D(2), F.Id("i")), F.D(1));
        Formula sinTaylor = SumRange(F.D(1, 0),
            Fraction(
                Multiply(Power(ParenthesizedNegative(F.D(1)), F.Id("i")),
                    Power(r0, sinDegree)),
                Factorial(sinDegree)));
        Formula hypotheses = AndAll(
            LessOrEqual(v, F.D(6, 0)),
            LessOrEqual(betaLo, BetaAffine(v, PhiLo())),
            LessOrEqual(BetaAffine(v, PhiHi()), betaHi),
            LessOrEqual(F.D(0), betaLo),
            LessOrEqual(xLo, Multiply(Multiply(RealPart(F.Id("c")), betaLo), LogLo())),
            LessOrEqual(Multiply(Multiply(RealPart(F.Id("c")), betaHi), LogHi()), xHi),
            LessOrEqual(thetaLo,
                Multiply(Multiply(ImaginaryPart(F.Id("c")), betaLo), LogLo())),
            LessOrEqual(
                Multiply(Multiply(ImaginaryPart(F.Id("c")), betaHi), LogHi()), thetaHi),
            LessOrEqual(phaseLo, Conditional(swap,
                Subtract(Subtract(thetaLo, Fraction(F.Id("piApprox"), F.D(2))),
                    Fraction(F.D(1), Multiply(F.D(2), Power(F.Seq(F.D(1, 0)), F.D(1, 9))))),
                thetaLo)),
            LessOrEqual(Conditional(swap,
                Add(Subtract(thetaHi, Fraction(F.Id("piApprox"), F.D(2))),
                    Fraction(F.D(1), Multiply(F.D(2), Power(F.Seq(F.D(1, 0)), F.D(1, 9))))),
                thetaHi), phaseHi),
            Less(F.D(0), scale),
            LessOrEqual(qLo, Fraction(Negate(xHi), scale)),
            LessOrEqual(Fraction(Negate(xLo), scale), qHi),
            LessOrEqual(Absolute(qLo), F.D(1)),
            LessOrEqual(Absolute(qHi), F.D(1)),
            LessOrEqual(baseLo, expTaylorLo),
            LessOrEqual(expTaylorHi, baseHi),
            LessOrEqual(F.D(0), baseLo),
            LessOrEqual(expLo, Power(baseLo, scale)),
            LessOrEqual(Power(baseHi, scale), expHi),
            LessOrEqual(Subtract(exp0, expErr), expLo),
            LessOrEqual(expHi, Add(exp0, expErr)),
            LessOrEqual(Absolute(phaseLo), Power(F.Seq(F.D(1, 0)), F.D(7))),
            LessOrEqual(
                Add(Absolute(Subtract(phaseLo, Multiply(phaseIndex, F.Id("piApprox")))),
                    Subtract(phaseHi, phaseLo)),
                Fraction(F.D(9, 9), F.D(1, 0, 0))),
            LessOrEqual(Multiply(Absolute(phaseIndex), InversePowerTen(19)), piErr),
            Equal(r0, Subtract(Fraction(Add(phaseLo, phaseHi), F.D(2)),
                Multiply(phaseIndex, F.Id("piApprox")))),
            LessOrEqual(Add(Fraction(Subtract(phaseHi, phaseLo), F.D(2)), piErr), rDelta),
            LessOrEqual(Absolute(r0), F.D(1)),
            LessOrEqual(Add(
                Fraction(Power(Absolute(r0), F.D(2, 0)), Factorial(F.D(2, 0))),
                Absolute(Subtract(cosTaylor, cos0))), cosBaseErr),
            LessOrEqual(Add(
                Fraction(Power(Absolute(r0), F.D(2, 1)), Factorial(F.D(2, 1))),
                Absolute(Subtract(sinTaylor, sin0))), sinBaseErr),
            LessOrEqual(Add(rDelta, cosBaseErr), cosErr),
            LessOrEqual(Add(rDelta, sinBaseErr), sinErr),
            Equal(Conditional(swap,
                Multiply(ParenthesizedNegative(sign), sin0), Multiply(sign, cos0)),
                thetaCos0),
            Equal(Conditional(swap, Multiply(sign, cos0), Multiply(sign, sin0)), thetaSin0),
            LessOrEqual(Conditional(swap, sinErr, cosErr), thetaCosErr),
            LessOrEqual(Conditional(swap, cosErr, sinErr), thetaSinErr),
            LessOrEqual(reLo, Subtract(Multiply(exp0, thetaCos0),
                Add(expErr, Multiply(Absolute(exp0), thetaCosErr)))),
            LessOrEqual(Add(Multiply(exp0, thetaCos0),
                Add(expErr, Multiply(Absolute(exp0), thetaCosErr))), reHi),
            LessOrEqual(imLo, Subtract(Negate(Multiply(exp0, thetaSin0)),
                Add(expErr, Multiply(Absolute(exp0), thetaSinErr)))),
            LessOrEqual(Add(Negate(Multiply(exp0, thetaSin0)),
                Add(expErr, Multiply(Absolute(exp0), thetaSinErr))), imHi),
            LessOrEqual(Subtract(reHi, reLo), InversePowerTen(15)),
            LessOrEqual(Subtract(imHi, imLo), InversePowerTen(15)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("v", Naturals()), Bound("scale", Naturals()),
                Bound("swap", F.Id("Bool")),
                .. RationalBounds(
                    "betaLo", "betaHi", "xLo", "xHi", "thetaLo", "thetaHi",
                    "phaseLo", "phaseHi", "r0", "rDelta", "piErr", "qLo", "qHi",
                    "baseLo", "baseHi", "expLo", "expHi", "exp0", "expErr",
                    "cos0", "sin0", "cosBaseErr", "sinBaseErr", "cosErr", "sinErr",
                    "thetaCos0", "thetaSin0", "thetaCosErr", "thetaSinErr",
                    "termReLo", "termReHi", "termImLo", "termImHi"),
            ],
            Implies(hypotheses, TermConclusion(v, reLo, reHi, imLo, imHi))));
    }

    private static Formula ModeDerivativeFormula()
    {
        Formula v = F.Id("v"), betaLo = F.Id("betaLo"), betaHi = F.Id("betaHi");
        Formula exp0 = F.Id("exp0"), thetaCos0 = F.Id("thetaCos0");
        Formula thetaSin0 = F.Id("thetaSin0");
        Formula termReErr = F.Id("termReErr"), termImErr = F.Id("termImErr");
        Formula termReLo = F.Id("termReLo"), termReHi = F.Id("termReHi");
        Formula termImLo = F.Id("termImLo"), termImHi = F.Id("termImHi");
        Formula amp0 = F.Id("amp0"), ampErr = F.Id("ampErr");
        Formula reLo = F.Id("derivReLo"), reHi = F.Id("derivReHi");
        Formula imLo = F.Id("derivImLo"), imHi = F.Id("derivImHi");
        Formula hypotheses = AndAll(
            LessOrEqual(v, F.D(6, 0)),
            LessOrEqual(betaLo, BetaAffine(v, PhiLo())),
            LessOrEqual(BetaAffine(v, PhiHi()), betaHi),
            LessOrEqual(F.D(0), betaLo),
            TermConclusion(v, termReLo, termReHi, termImLo, termImHi),
            LessOrEqual(Subtract(amp0, ampErr), Multiply(LogLo(), betaLo)),
            LessOrEqual(Multiply(LogHi(), betaHi), Add(amp0, ampErr)),
            LessOrEqual(Subtract(Multiply(exp0, thetaCos0), termReErr), termReLo),
            LessOrEqual(termReHi, Add(Multiply(exp0, thetaCos0), termReErr)),
            LessOrEqual(Subtract(Negate(Multiply(exp0, thetaSin0)), termImErr), termImLo),
            LessOrEqual(termImHi, Add(Negate(Multiply(exp0, thetaSin0)), termImErr)),
            LessOrEqual(reLo, Subtract(Negate(Multiply(amp0, Multiply(exp0, thetaCos0))),
                Add(ampErr, Multiply(Absolute(amp0), termReErr)))),
            LessOrEqual(Add(Negate(Multiply(amp0, Multiply(exp0, thetaCos0))),
                Add(ampErr, Multiply(Absolute(amp0), termReErr))), reHi),
            LessOrEqual(imLo,
                Subtract(Negate(Multiply(amp0, Negate(Multiply(exp0, thetaSin0)))),
                    Add(ampErr, Multiply(Absolute(amp0), termImErr)))),
            LessOrEqual(
                Add(Negate(Multiply(amp0, Negate(Multiply(exp0, thetaSin0)))),
                    Add(ampErr, Multiply(Absolute(amp0), termImErr))), imHi),
            LessOrEqual(Subtract(reHi, reLo), InversePowerTen(15)),
            LessOrEqual(Subtract(imHi, imLo), InversePowerTen(15)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("v", Naturals()),
                .. RationalBounds(
                    "betaLo", "betaHi", "exp0", "thetaCos0", "thetaSin0",
                    "termReErr", "termImErr", "termReLo", "termReHi", "termImLo",
                    "termImHi", "amp0", "ampErr", "derivReLo", "derivReHi",
                    "derivImLo", "derivImHi"),
            ],
            Implies(hypotheses, DerivativeConclusion(v, reLo, reHi, imLo, imHi))));
    }

    private static Formula TermConclusion(
        Formula v,
        Formula reLo,
        Formula reHi,
        Formula imLo,
        Formula imHi)
    {
        Formula term = ModeTerm(v);
        return And(
            And(Between(reLo, RealPart(term), reHi),
                Between(imLo, ImaginaryPart(term), imHi)),
            And(LessOrEqual(Subtract(reHi, reLo), InversePowerTen(15)),
                LessOrEqual(Subtract(imHi, imLo), InversePowerTen(15))));
    }

    private static Formula DerivativeConclusion(
        Formula v,
        Formula reLo,
        Formula reHi,
        Formula imLo,
        Formula imHi)
    {
        Formula derivative = ModeDerivative(v);
        return And(
            And(Between(reLo, RealPart(derivative), reHi),
                Between(imLo, ImaginaryPart(derivative), imHi)),
            And(LessOrEqual(Subtract(reHi, reLo), InversePowerTen(15)),
                LessOrEqual(Subtract(imHi, imLo), InversePowerTen(15))));
    }

    private static Formula ModeTerm(Formula v) =>
        Power(
            F.Seq(F.D(2)),
            ParenthesizedNegative(Multiply(F.Id("c"), Call("beta", v))));

    private static Formula ModeDerivative(Formula v) =>
        Multiply(
            Multiply(ParenthesizedNegative(Call("beta", v)), Call("log", F.D(2))),
            ModeTerm(v));

    private static Formula BetaAffine(Formula v, Formula phiBound) =>
        Add(Subtract(Subtract(Call("o5FloorTable", v), F.D(1)), v), Multiply(v, phiBound));

    private static Formula PhiLo() => Fraction(
        F.D(8, 0, 9, 0, 1, 6, 9, 9, 4, 3, 7, 4, 9, 4, 7, 4, 2, 4, 1),
        F.D(5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0));

    private static Formula PhiHi() => Fraction(
        F.D(1, 6, 1, 8, 0, 3, 3, 9, 8, 8, 7, 4, 9, 8, 9, 4, 8, 4, 8, 2, 1),
        F.D(1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0));

    private static Formula LogLo() => Fraction(
        F.D(
            8, 1, 0, 2, 6, 2, 0, 4, 9, 4, 6, 9, 1, 4, 2, 7, 2, 6, 1, 8,
            2, 4, 7, 5, 9, 4, 2, 3, 0, 5, 5, 8, 6, 3, 9, 4, 3, 6, 2, 1,
            0, 8, 3, 1, 1, 9, 5),
        F.D(
            1, 1, 6, 8, 9, 6, 1, 0, 4, 0, 5, 8, 9, 6, 6, 0, 1, 5, 6, 4,
            6, 7, 5, 0, 9, 4, 7, 5, 5, 4, 9, 7, 8, 3, 1, 4, 9, 8, 7, 9,
            9, 2, 2, 5, 2, 4, 1, 6));

    private static Formula LogHi() => Fraction(
        F.D(
            8, 1, 0, 2, 6, 2, 0, 4, 9, 4, 6, 9, 1, 4, 2, 7, 2, 6, 1, 8,
            4, 4, 5, 6, 2, 3, 9, 3, 3, 6, 4, 5, 8, 6, 2, 1, 6, 6, 0, 1,
            8, 9, 8, 4, 2, 6, 3),
        F.D(
            1, 1, 6, 8, 9, 6, 1, 0, 4, 0, 5, 8, 9, 6, 6, 0, 1, 5, 6, 4,
            6, 7, 5, 0, 9, 4, 7, 5, 5, 4, 9, 7, 8, 3, 1, 4, 9, 8, 7, 9,
            9, 2, 2, 5, 2, 4, 1, 6));

    private static Formula Between(Formula lo, Formula value, Formula hi) =>
        And(LessOrEqual(lo, value), LessOrEqual(value, hi));

    private static Formula InversePowerTen(int exponent) =>
        Fraction(F.D(1), Power(
            F.Seq(F.D(1, 0)),
            F.D((byte)(exponent / 10), (byte)(exponent % 10))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Power(Formula value, Formula exponent) =>
        F.Seq(F.Grp(value), F.Caret, F.Grp(exponent));

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Negate(Formula value) => new Formula.Negate(value);

    private static Formula ParenthesizedNegative(Formula value) =>
        F.Seq(F.Open, F.Minus, value, F.Close);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula AndAll(params Formula[] values)
    {
        Formula result = values[^1];
        for (int i = values.Length - 2; i >= 0; i--)
        {
            result = And(values[i], result);
        }
        return result;
    }

    private static Formula Absolute(Formula value) => new Formula.Absolute(value);

    private static Formula RealPart(Formula value) => F.Seq(F.Re, F.Grp(value));

    private static Formula ImaginaryPart(Formula value) => Call("Im", value);

    private static Formula Factorial(Formula value) => Call("factorial", value);

    private static Formula SumRange(Formula limit, Formula summand) =>
        F.Seq(F.Sum, F.Underscore,
            F.Grp(F.Id("i"), F.InMacro, Call("range", limit)), F.Sp, summand);

    private static Formula Conditional(
        Formula condition,
        Formula whenTrue,
        Formula whenFalse) =>
        F.Seq(
            F.Text, F.Grp(F.Id("if")), F.Sp, condition, F.Sp,
            F.Text, F.Grp(F.Id("then")), F.Sp, whenTrue, F.Sp,
            F.Text, F.Grp(F.Id("else")), F.Sp, whenFalse);

    private static Formula.BoundVariable[] RationalBounds(params string[] names) =>
        [.. names.Select(name => Bound(name, Rationals()))];

    private static Formula Naturals() => F.Seq(F.Mathbb, F.Grp(F.Id("N")));

    private static Formula Rationals() => F.Seq(F.Mathbb, F.Grp(F.Id("Q")));
}
