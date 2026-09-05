using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class UnifiedPinchingFeeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A binary-entropy pinching fee has one transition profile joining its pure- and mixed-state asymptotics.",
        H("Unified Pinching Fee"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-singular-boundary-remainder-vanishes"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumChannels/UnifiedPinchingFee."
                        + "singular_boundary_error_limit"),
                H("The singular boundary remainder vanishes"),
                StatementSource.FromAuthor(SingularRemainderFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every nonnegative transition coordinate x, the singular part of the "
                            + "binary-entropy increment differs from its explicit logarithmic profile "
                            + "by a quantity tending to zero as the scale tends to zero from above.")),
                    Paragraph(Text(
                        "This is the analytic remainder estimate used on the live derivation path. "
                            + "It follows from continuity of y log y at zero and a first-order "
                            + "calculation for the boundary eigenvalue."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("the-unified-pinching-fee-law"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumChannels/UnifiedPinchingFee.unified_pinching_fee_law"),
                H("The unified pinching-fee law"),
                StatementSource.FromAuthor(UnifiedLawFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let t = delta squared over four, u = 1-r, and x = u/(2t). These source "
                            + "coordinates are the public definitions handTremor, doorGap, and "
                            + "transitionCoordinate. The fee is the exact binary-entropy increment "
                            + "quadraticPinchingFee, not a function defined by the target asymptotic.")),
                    Paragraph(Text(
                        "Along r = 1-2tx, the quotient of the exact fee by t times the displayed "
                            + "transition coefficient tends to one. The scale-independent correction "
                            + "tends to one at x approaching zero from above, giving the pure-state "
                            + "logarithmic law.")),
                    Paragraph(Text(
                        "At the mixed-state end, substituting t = u/(2x) makes the transition "
                            + "coefficient tend to log(2/u). For fixed 0<r<1 and t=delta squared over "
                            + "four, the fee divided by delta squared tends to r artanh(r)/2.")),
                    Paragraph(Text(
                        "The source's numerical crossover ratio 1.0000 to 0.9946 is an empirical "
                            + "remark and is outside this theorem."))),
                DescribeRole.Theorem))));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula PositiveFilter() =>
        Call("nhdsWithin", D(0), Call("Ioi", D(0)));

    private static Formula Neighborhood(Formula value) => Call("nhds", value);

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula Mul(Formula left, Formula right) =>
        Seq(left, Sp, Cdot, Sp, right);

    private static Formula Div(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Add(Formula left, Formula right) =>
        Seq(left, Sp, Plus, Sp, right);

    private static Formula Subtract(Formula left, Formula right) =>
        Seq(left, Sp, Minus, Sp, right);

    private static Formula Tendsto(Formula function, Formula source, Formula target) =>
        Call("Tendsto", function, source, target);

    private static Formula SingularRemainderFormula()
    {
        Formula real = Reals();
        Formula x = F.Id("x");
        Formula t = F.Id("t");
        Formula upper = Call("boundaryUpperProbability", t, x);
        Formula tx = Mul(t, x);
        Formula singularDifference = Div(
            Subtract(Call("negMulLog", upper), Call("negMulLog", tx)),
            t);
        Formula inverseT = Power(t, Seq(Minus, D(1)));
        Formula xPlusOne = Add(x, D(1));
        Formula logarithmicProfile = Subtract(
            Add(Call("log", inverseT), Mul(x, Call("log", x))),
            Mul(Grp(xPlusOne), Call("log", xPlusOne)));
        Formula remainder = Subtract(singularDifference, Grp(logarithmicProfile));
        Formula limit = Tendsto(
            Lambda(Typed(t, real), remainder),
            PositiveFilter(),
            Neighborhood(D(0)));

        return Disp(Seq(
            Forall, Sp, Typed(x, real), Comma, Sp,
            D(0), Sp, Leq, Sp, x, Sp, Rightarrow, Sp, limit, Dot));
    }

    private static Formula UnifiedLawFormula()
    {
        Formula real = Reals();
        Formula x = F.Id("x");
        Formula r = F.Id("r");
        Formula t = F.Id("t");
        Formula y = F.Id("y");
        Formula delta = F.Id("delta");

        Formula transition = Call("transitionLeading", t, x);
        Formula uniformRatio = Div(
            Call("boundaryPinchingFee", t, x),
            Mul(t, transition));
        Formula uniformLimit = Tendsto(
            Lambda(Typed(t, real), uniformRatio),
            PositiveFilter(),
            Neighborhood(D(1)));

        Formula pureLimit = Tendsto(
            F.Id("transitionCorrection"),
            PositiveFilter(),
            Neighborhood(D(1)));

        Formula gap = Call("doorGap", r);
        Formula mixedScale = Div(gap, Mul(D(2), y));
        Formula mixedLimit = Tendsto(
            Lambda(Typed(y, real), Call("transitionLeading", mixedScale, y)),
            F.Id("atTop"),
            Neighborhood(Call("log", Div(D(2), gap))));

        Formula deltaSquared = Power(delta, D(2));
        Formula coefficientLimit = Tendsto(
            Lambda(
                Typed(delta, real),
                Div(
                    Call("quadraticPinchingFee", r, Call("handTremor", delta)),
                    deltaSquared)),
            PositiveFilter(),
            Neighborhood(Div(Mul(r, Call("artanh", r)), D(2))));

        Formula hypotheses = Seq(
            D(0), Sp, Leq, Sp, x, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, r, Sp, Land, Sp,
            r, Sp, Lt, Sp, D(1));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(x, real), Comma, Sp, Typed(r, real), Comma, Sp,
                hypotheses, Sp, Rightarrow),
            Seq(Grp(), uniformLimit, Sp, Land),
            Seq(Grp(), pureLimit, Sp, Land),
            Seq(Grp(), mixedLimit, Sp, Land),
            Seq(Grp(), coefficientLimit, Dot),
        ]));
    }
}
