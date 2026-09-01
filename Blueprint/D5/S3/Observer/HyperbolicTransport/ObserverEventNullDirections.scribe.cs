using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.HyperbolicTransport;

internal sealed class ObserverEventNullDirectionsDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/HyperbolicTransport/ObserverEventNullDirections."
            + "golden_observer_event_null_directions";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden observer events and their genuine tangents recover two fixed null directions.",
        H("Golden Observer Events and Null Directions"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-observer-event-null-directions"),
            DeclarationHandle.Create(Declaration),
            H("Observer events and tangents recover the golden null basis"),
            StatementSource.FromAuthor(EventFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The two vectors (phi,1) and (phi-prime,1) form a basis of the real "
                        + "plane. Every vector therefore has unique coefficients in this basis, "
                        + "and the golden Lorentz form of a combination is exactly -5ab.")),
                Paragraph(Text(
                    "The displayed event and tangent are defined from positive exponential "
                        + "amplitudes divided by sqrt(5). The proof establishes sqrt(5)>0 "
                        + "internally, differentiates both event coordinates, and proves that "
                        + "the event remains on the unit Lorentz hyperbola.")),
                Paragraph(Text(
                    "Adding the tangent to the event cancels the conjugate direction; "
                        + "subtracting the event from the tangent cancels the future direction. "
                        + "The remaining amplitudes are strictly positive for every rapidity.")),
                Paragraph(Text(
                    "At zero rapidity all eight event laws give a concrete satisfying witness. "
                        + "Replacing the genuine tangent there by the zero vector falsifies the "
                        + "future-null identity, so the derivative clauses are not vacuous."))),
            DescribeRole.Theorem))));

    private static Formula EventFormula()
    {
        Formula real = Call("Real");
        Formula vector = Call("Prod", real, real);
        Formula eta = F.Id("eta");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula v = F.Id("v");
        Formula qArgument = F.Id("w");
        Formula phi = Varphi;
        Formula phiPrime = Seq(Varphi, Apos);
        Formula futureNull = F.Id("uPlus");
        Formula pastNull = F.Id("uMinus");
        Formula futureNullDefinition = Call("pair", phi, D(1));
        Formula pastNullDefinition = Call("pair", phiPrime, D(1));
        Formula q = F.Id("Q");
        Formula sqrtFive = Call("sqrt", D(5));
        Formula expEta = Call("exp", eta);
        Formula expNegEta = Call("exp", Neg(eta));
        Formula observerEvent = Call("h", eta);
        Formula tangent = Call("tangent", eta);
        Formula eventDefinition = Call(
            "pair",
            new Formula.Fraction(
                Subtract(Multiply(expEta, phi), Multiply(expNegEta, phiPrime)),
                sqrtFive),
            new Formula.Fraction(Subtract(expEta, expNegEta), sqrtFive));
        Formula tangentDefinition = Call(
            "pair",
            new Formula.Fraction(
                Add(Multiply(expEta, phi), Multiply(expNegEta, phiPrime)),
                sqrtFive),
            new Formula.Fraction(Add(expEta, expNegEta), sqrtFive));
        Formula futureAmplitude = new Formula.Fraction(expEta, sqrtFive);
        Formula signedPastAmplitude = Neg(new Formula.Fraction(expNegEta, sqrtFive));
        Formula pastAmplitude = new Formula.Fraction(expNegEta, sqrtFive);
        Formula twiceFutureAmplitude =
            new Formula.Fraction(Multiply(D(2), expEta), sqrtFive);
        Formula twicePastAmplitude =
            new Formula.Fraction(Multiply(D(2), expNegEta), sqrtFive);
        Formula coordinateVector = Add(Scale(a, futureNull), Scale(b, pastNull));
        Formula uniqueCoordinates = Seq(
            Forall, Sp, v, InMacro, Sp, vector, Comma, Esc,
            Exists, Sp, Bang, Sp, a, Comma, Sp, b, InMacro, Sp, real, Comma, Esc,
            v, Sp, Eq, Sp, coordinateVector);
        Formula coordinateLaw = ForAll(
            [Bound("a", real), Bound("b", real)],
            Equal(Apply(q, coordinateVector), Neg(Multiply(Multiply(D(5), a), b))));
        Formula nullLaws = And(
            Equal(Apply(q, futureNull), D(0)),
            Equal(Apply(q, pastNull), D(0)));
        Formula eventLaws = ForAll(
            [Bound("eta", real)],
            All(
                Equal(observerEvent, Add(
                    Scale(futureAmplitude, futureNull),
                    Scale(signedPastAmplitude, pastNull))),
                Equal(tangent, Add(
                    Scale(futureAmplitude, futureNull),
                    Scale(pastAmplitude, pastNull))),
                Call("HasDerivAt", F.Id("h"), tangent, eta),
                Equal(Apply(q, observerEvent), D(1)),
                Equal(Add(observerEvent, tangent), Scale(twiceFutureAmplitude, futureNull)),
                Equal(Subtract(tangent, observerEvent), Scale(twicePastAmplitude, pastNull)),
                Less(D(0), twiceFutureAmplitude),
                Less(D(0), twicePastAmplitude)));
        Formula qFirst = Call("fst", qArgument);
        Formula qSecond = Call("snd", qArgument);
        Formula qDefinition = Subtract(
            Subtract(new Formula.Power(qFirst, D(2)), Multiply(qFirst, qSecond)),
            new Formula.Power(qSecond, D(2)));

        return Disp(Seq(
            F.Id("let"), Sp, futureNull, Sp, Eq, Sp, futureNullDefinition, Semi,
            RowBreak,
            F.Id("let"), Sp, pastNull, Sp, Eq, Sp, pastNullDefinition, Semi,
            RowBreak,
            F.Id("let"), Sp, q, Open, qArgument, Close, Sp, Eq, Sp,
            qDefinition, Semi, RowBreak,
            F.Id("let"), Sp, observerEvent, Sp, Eq, Sp, eventDefinition, Semi, RowBreak,
            F.Id("let"), Sp, tangent, Sp, Eq, Sp, tangentDefinition, Semi, RowBreak,
            All(Grp(uniqueCoordinates), coordinateLaw, nullLaws, eventLaws), Dot));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(
        Formula.BoundVariable[] variables,
        Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Scale(Formula scalar, Formula vector) =>
        Seq(scalar, Sp, Cdot, Sp, vector);

    private static Formula Neg(Formula value) => Seq(Minus, value);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula All(params Formula[] formulas) =>
        formulas.Aggregate(And);
}
