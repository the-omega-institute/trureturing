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
                        "The source scales t = delta squared over four and u = 1-r are exposed by "
                            + "handTremor and doorGap. The relation r = 1-2tx is exposed by "
                            + "boundaryRadius, while the third conjunct uses its inverse substitution "
                            + "t = doorGap(r)/(2x). The fee model quadraticPinchingFee is the "
                            + "binary-entropy increment H2((1-r)/2 + r*t) - H2((1-r)/2). "
                            + "No public declaration identifies the source's tilted-pinching fee "
                            + "with this model; the source-fee clauses remain conditional on that "
                            + "uncarried identification.")),
                    Paragraph(Text(
                        "Along r = 1-2tx, the quotient of the fee model by t times the displayed "
                            + "transition coefficient tends to one. The scale-independent correction "
                            + "tends to one at x approaching zero from above, giving the pure-state "
                            + "logarithmic law.")),
                    Paragraph(Text(
                        "At the mixed-state end, substituting t = u/(2x) makes the transition "
                            + "coefficient tend to log(2/u). For fixed 0<r<1 and t=delta squared over "
                            + "four, the model divided by delta squared tends to r artanh(r)/2; this "
                            + "fourth limit is the model's formal first-order content. The fixed-x fee ratio "
                            + "and the x-to-infinity profile formalize separate regimes and are not "
                            + "composed into a single limit.")),
                    Paragraph(Text(
                        "The source's 'that is' bridge is carried in the gate-closing regime: as r "
                            + "approaches one from below, the ratio of 2r artanh(r) to "
                            + "log(2/(1-r)) tends to one. The coefficients are not asserted equal at "
                            + "a fixed mixed-state radius.")),
                    Paragraph(Text(
                        "The source sentence reporting a numerical crossover ratio from 1.0000 to "
                            + "0.9946 is computational-experiment content and is not formalized."))),
                DescribeRole.Theorem))));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula PositiveFilter() =>
        Call("nhdsWithin", D(0), Call("Ioi", D(0)));

    private static Formula LeftFilter() =>
        Call("nhdsWithin", D(1), Call("Iio", D(1)));

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
            Mul(Seq(Open, xPlusOne, Close), Call("log", xPlusOne)));
        Formula remainder = Subtract(singularDifference, Seq(Open, logarithmicProfile, Close));
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

        Formula bridgeLimit = Tendsto(
            Lambda(
                Typed(r, real),
                Div(
                    Mul(Mul(D(2), r), Call("artanh", r)),
                    Call("log", Div(D(2), Subtract(D(1), r))))),
            LeftFilter(),
            Neighborhood(D(1)));

        Formula scopedUniformLimit = Seq(
            Forall, Sp, Typed(x, real), Comma, Sp,
            D(0), Sp, Leq, Sp, x, Sp, Rightarrow, Sp, uniformLimit);

        Formula scopedMixedLimit = Seq(
            Forall, Sp, Typed(r, real), Comma, Sp,
            r, Sp, Lt, Sp, D(1), Sp, Rightarrow, Sp, mixedLimit);

        Formula scopedCoefficientLimit = Seq(
            Forall, Sp, Typed(r, real), Comma, Sp,
            D(0), Sp, Lt, Sp, r, Sp, Rightarrow, Sp,
            r, Sp, Lt, Sp, D(1), Sp, Rightarrow, Sp, coefficientLimit);

        return Disp(new Formula.Aligned([
            Seq(Grp(), Open, scopedUniformLimit, Close, Sp, Land),
            Seq(Grp(), pureLimit, Sp, Land),
            Seq(Grp(), Open, scopedMixedLimit, Close, Sp, Land),
            Seq(Grp(), Open, scopedCoefficientLimit, Close, Sp, Land),
            Seq(Grp(), bridgeLimit, Dot),
        ]));
    }
}
