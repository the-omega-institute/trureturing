using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class OrderedPrimeHolonomyCasimirDocument
    : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Observer/AgencyHolonomy/OrderedPrimeHolonomyCasimir.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordered-prime observer trace cancels linear phase and retains the squared winding response.",
        H("Ordered-Prime Holonomy Casimir"),
        Blocks(Describe.Lean(
            DescribeId.Create("ordered-prime-holonomy-casimir"),
            DeclarationHandle.Create(Handle + "ordered_prime_holonomy_casimir"),
            H("Linear cancellation and quadratic winding readout"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Each primitive orbit carries its actual ordered prime word and an integral "
                        + "rotation winding. The orientation premise identifies the imported "
                        + "prime-word holonomy with that rotation in the infinite dihedral group.")),
                Paragraph(Text(
                    "The observer uses the two conjugate Fourier channels, the product prime "
                        + "weight, and every positive repeat. Summability of the weight and its "
                        + "first two winding moments supplies the absolute-convergence region.")),
                Paragraph(Text(
                    "The local negative second trace derivative is twice the squared repeated "
                        + "winding. Globally the first derivative vanishes, while the negative "
                        + "second derivative is the nonnegative weighted sum of all repeated "
                        + "squared windings."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula orbitType = F.Id("iota");
        Formula word = F.Id("word");
        Formula winding = F.Id("winding");
        Formula spectral = F.Id("s");
        Formula orbit = F.Id("i");
        Formula repeat = F.Id("m");
        Formula repeatedOrbit = F.Id("x");
        Formula theta = F.Id("theta");
        Formula type = F.Seq(F.Operatorname, F.Grp(F.Id("Type")));
        Formula real = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        Formula natural = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        Formula prime = Call("UnramifiedPrime");
        Formula wordType = Call("List", prime);
        Formula windingType = Call("ZMod", F.D(0));
        Formula repeatedOrbitType = F.Grp(
            orbitType, F.Sp, F.Times, F.Sp, natural);

        Formula WordAt(Formula value) => Apply(word, value);
        Formula WindingAt(Formula value) => Apply(winding, value);
        Formula Holonomy(Formula value) =>
            Apply(F.Id("goldenPrimeHolonomy"), WordAt(value));
        Formula Amplitude(Formula value) =>
            Call("observerOrbitAmplitude", word, spectral, value);
        Formula Frequency(Formula value) =>
            Call("repeatedOrbitWinding", winding, value);
        Formula ObserverLog() => Call("orderedPrimeObserverLog", word, spectral);
        Formula IteratedDerivative(byte order, Formula function) =>
            Call("iteratedDeriv", F.D(order), function, F.D(0));
        Formula Square(Formula value) => new Formula.Power(value, F.D(2));
        Formula Twice(Formula value) => Multiply(F.D(2), value);
        Formula Readout(Formula value) =>
            Multiply(Amplitude(value), Twice(Square(Frequency(value))));

        Formula orientation = ForAll(
            [Bound("i", orbitType)],
            Equal(Holonomy(orbit), Call("r", WindingAt(orbit))));
        Formula weightSummable = Call(
            "Summable",
            Lambda(repeatedOrbit, repeatedOrbitType,
                Call("abs", Amplitude(repeatedOrbit))));
        Formula linearMomentSummable = Call(
            "Summable",
            Lambda(repeatedOrbit, repeatedOrbitType,
                Multiply(
                    Call("abs", Amplitude(repeatedOrbit)),
                    Twice(Call("abs", Frequency(repeatedOrbit))))));
        Formula squareMomentSummable = Call(
            "Summable",
            Lambda(repeatedOrbit, repeatedOrbitType,
                Multiply(
                    Call("abs", Amplitude(repeatedOrbit)),
                    Twice(Square(Frequency(repeatedOrbit))))));

        Formula poweredHolonomy = new Formula.Power(Holonomy(orbit), repeat);
        Formula representedHolonomy = Apply(
            Call("dihedralObserverRepresentation", theta),
            poweredHolonomy);
        Formula localTraceFunction = Lambda(
            theta,
            real,
            Call("re", Call("trace", representedHolonomy)));
        Formula castWinding = Call("integerCast", WindingAt(orbit));
        Formula localCasimir = ForAll(
            [Bound("i", orbitType), Bound("m", natural)],
            Equal(
                new Formula.Negate(IteratedDerivative(2, localTraceFunction)),
                Multiply(Twice(Square(repeat)), Square(castWinding))));
        Formula linearCancellation = Equal(
            IteratedDerivative(1, ObserverLog()),
            F.D(0));
        Formula squareReadout = Equal(
            new Formula.Negate(IteratedDerivative(2, ObserverLog())),
            Call("tsum", Lambda(repeatedOrbit, repeatedOrbitType,
                Readout(repeatedOrbit))));
        Formula positivity = ForAll(
            [Bound("x", repeatedOrbitType)],
            new Formula.Relation(
                F.D(0),
                FormulaRelationOperator.LessThanOrEqual,
                Readout(repeatedOrbit)));

        Formula premises = All(
            Call("Countable", orbitType),
            orientation,
            weightSummable,
            linearMomentSummable,
            squareMomentSummable);
        Formula conclusions = All(
            localCasimir,
            linearCancellation,
            squareReadout,
            positivity);

        return F.Disp(ForAll(
            [
                Bound("iota", type),
                Bound("word", Arrow(orbitType, wordType)),
                Bound("winding", Arrow(orbitType, windingType)),
                Bound("s", real),
            ],
            new Formula.Logic(
                premises,
                FormulaLogicOperator.Implies,
                conclusions)));
    }

    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);

    private static Formula ForAll(
        Formula.BoundVariable[] variables,
        Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Lambda(Formula name, Formula type, Formula body) =>
        F.Seq(
            F.Open, name, F.Colon, F.Sp, type, F.Sp, F.Mapsto, F.Sp,
            body, F.Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
        {
            result = new Formula.Logic(
                clauses[index], FormulaLogicOperator.And, result);
        }

        return result;
    }
}
