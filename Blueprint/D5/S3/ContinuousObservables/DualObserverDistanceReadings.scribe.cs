using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ContinuousObservables;

internal sealed class DualObserverDistanceReadingsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two bounded-function observers assign a typed extended-distance reading to the same endpoints.",
        H("Dual Observer Distance Readings"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dual-observer-distance-readings"),
                DeclarationHandle.Create(
                    "D5/S3/ContinuousObservables/DualObserverDistanceReadings."
                        + "dual_observer_distance_readings"),
                H("One endpoint pair has two typed observer readings"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The observable carriers are real subspaces of the bounded functions on the state set. Each cost is homogeneous under real scaling, and each distance is the supremum of endpoint gaps over its unit-cost ball.")),
                    Paragraph(Text(
                        "When that unit ball spans its observable space, zero distance is exactly equality of all accessible readouts. A zero-cost observable that separates the endpoints can be scaled without cost and therefore forces infinite distance."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula extended = Seq(OpenBracket, D(0), Comma, Sp, Infty, CloseBracket);
        Formula state = F.Id("X");
        Formula first = F.Id("A");
        Formula second = F.Id("APrime");
        Formula firstCost = F.Id("L");
        Formula secondCost = F.Id("LPrime");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula firstDistance = new Formula.Subscript(F.Id("d"), F.Id("O"));
        Formula secondDistance = new Formula.Subscript(F.Id("d"), F.Id("OPrime"));
        Formula firstZero = new Formula.Subscript(F.Id("Z"), F.Id("O"));
        Formula secondZero = new Formula.Subscript(F.Id("Z"), F.Id("OPrime"));
        Formula firstDetector = new Formula.Subscript(F.Id("H"), F.Id("O"));
        Formula secondDetector = new Formula.Subscript(F.Id("H"), F.Id("OPrime"));
        Formula boundedFunctions = Call("ellInfty", state, real);
        Formula observableSpace = Call("Submodule", real, boundedFunctions);
        Formula costTypeFirst = Arrow(first, extended);
        Formula costTypeSecond = Arrow(second, extended);

        Formula firstZeroDefinition = ZeroMeaning(
            real, first, firstCost, firstDistance, x, y);
        Formula secondZeroDefinition = ZeroMeaning(
            real, second, secondCost, secondDistance, x, y);
        Formula firstDetectorDefinition = HorizonDetector(
            first, firstCost, firstDistance, x, y);
        Formula secondDetectorDefinition = HorizonDetector(
            second, secondCost, secondDistance, x, y);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(state, type), Comma, Sp,
                Typed(Seq(first, Comma, Sp, second), observableSpace), Comma),
            Seq(
                Grp(), Typed(firstCost, costTypeFirst), Comma, Sp,
                Typed(secondCost, costTypeSecond), Comma, Sp,
                Typed(Seq(x, Comma, Sp, y), state), Comma),
            Seq(
                Grp(), Open, Homogeneous(first, firstCost, real), Close,
                Sp, Land, Sp,
                Open, Homogeneous(second, secondCost, real), Close,
                Sp, Rightarrow),
            Seq(
                Grp(), Operatorname, Grp(F.Id("let")), Sp,
                firstDistance, Sp, Eq, Sp,
                Call("observerDistance", first, firstCost, x, y), Semi),
            Seq(
                Grp(), Operatorname, Grp(F.Id("let")), Sp,
                secondDistance, Sp, Eq, Sp,
                Call("observerDistance", second, secondCost, x, y), Semi),
            Seq(
                Grp(), Operatorname, Grp(F.Id("let")), Sp,
                firstZero, Sp, Eq, Sp, firstZeroDefinition, Semi),
            Seq(
                Grp(), Operatorname, Grp(F.Id("let")), Sp,
                secondZero, Sp, Eq, Sp, secondZeroDefinition, Semi),
            Seq(
                Grp(), Operatorname, Grp(F.Id("let")), Sp,
                firstDetector, Sp, Eq, Sp, firstDetectorDefinition, Semi),
            Seq(
                Grp(), Operatorname, Grp(F.Id("let")), Sp,
                secondDetector, Sp, Eq, Sp, secondDetectorDefinition),
            Seq(
                Grp(), Operatorname, Grp(F.Id("in")), Sp,
                Reading(firstDistance, firstZero, firstDetector), Sp, Land, Sp,
                Reading(secondDistance, secondZero, secondDetector), Dot),
        ]));
    }

    private static Formula Homogeneous(Formula observables, Formula cost, Formula real)
    {
        Formula scalar = F.Id("c");
        Formula observable = F.Id("f");
        return Seq(
            Forall, Sp, Typed(scalar, real), Comma, Sp,
            Typed(observable, observables), Comma, Sp,
            Apply(cost, Seq(scalar, observable)), Sp, Eq, Sp,
            new Formula.Absolute(scalar), Apply(cost, observable));
    }

    private static Formula ZeroMeaning(
        Formula real,
        Formula observables,
        Formula cost,
        Formula distance,
        Formula x,
        Formula y)
    {
        Formula observable = F.Id("f");
        Formula unitBall = Call("unitBall", observables, cost);
        Formula sameReadout = Seq(
            Forall, Sp, observable, Sp, InMacro, Sp, observables, Comma, Sp,
            Apply(observable, x), Sp, Eq, Sp, Apply(observable, y));
        return Seq(
            Call("span", real, unitBall), Sp, Eq, Sp, observables,
            Sp, Rightarrow, Sp,
            Open, distance, Sp, Eq, Sp, D(0), Sp, Iff, Sp, sameReadout, Close);
    }

    private static Formula HorizonDetector(
        Formula observables,
        Formula cost,
        Formula distance,
        Formula x,
        Formula y)
    {
        Formula observable = F.Id("f");
        return Seq(
            Open, Exists, Sp, observable, Sp, InMacro, Sp, observables, Comma, Sp,
            Apply(cost, observable), Sp, Eq, Sp, D(0), Sp, Land, Sp,
            Apply(observable, x), Sp, Neq, Sp, Apply(observable, y), Close,
            Sp, Rightarrow, Sp, distance, Sp, Eq, Sp, Infty);
    }

    private static Formula Reading(
        Formula distance,
        Formula zeroMeaning,
        Formula horizonDetector)
    {
        Formula meanings = Seq(zeroMeaning, Sp, Land, Sp, horizonDetector);
        return Seq(
            Open,
            Open, distance, Sp, Eq, Sp, D(0), Sp, Land, Sp, meanings, Close,
            Sp, Lor, Sp,
            Open, D(0), Sp, Lt, Sp, distance, Sp, Lt, Sp, Infty,
            Sp, Land, Sp, meanings, Close,
            Sp, Lor, Sp,
            Open, distance, Sp, Eq, Sp, Infty, Sp, Land, Sp, meanings, Close,
            Close);
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

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
