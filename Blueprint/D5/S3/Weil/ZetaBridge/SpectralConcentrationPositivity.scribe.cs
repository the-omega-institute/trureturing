using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class SpectralConcentrationPositivityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/ZetaBridge/SpectralConcentrationPositivity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A supremal band-concentration rate gives an explicit lower bound for a "
            + "spectrally weighted quadratic form and a strict positivity certificate.",
        H("Spectral Concentration Positivity"),
        Blocks(Describe.Lean(
            DescribeId.Create("spectral-concentration-positivity-certificate"),
            DeclarationHandle.Create(
                Prefix + "spectral_concentration_positivity_certificate"),
            H("Spectral concentration positivity certificate"),
            StatementSource.FromAuthor(CertificateFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The ratio set is built from the nonzero tests supported in the "
                        + "chosen spatial window. Its supremum is the concentration rate, "
                        + "while the weighted spectral integral is the quadratic form.")),
                Paragraph(Text(
                    "Nonnegative spectral density and Plancherel normalization bound every "
                        + "band ratio by one. Splitting the weighted integral over the band "
                        + "and its complement yields the displayed gap; the strict threshold "
                        + "then makes that gap positive on every supported nonzero test."))),
            DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, Formula value) =>
        Call("apply", function, value);

    private static Formula ApplyTwo(Formula function, Formula first, Formula second) =>
        Call("applyTwo", function, first, second);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }

    private static Formula Lambda(string name, Formula domain, Formula body) =>
        Seq(F.Id(name), Colon, Sp, domain, Sp, Mapsto, Sp, body);

    private static Formula Let(string name, Formula value) =>
        Seq(Operatorname, Grp(F.Id("let")), Sp, F.Id(name), Sp, Eq, Sp, value, Comma, Sp);

    private static Formula CertificateFormula()
    {
        Formula type = F.Id("Type"), prop = F.Id("Prop"), real = Call("Real");
        Formula test = F.Id("Test"), supported = F.Id("supportedIn");
        Formula mass = F.Id("spatialMass"), density = F.Id("spectralDensity");
        Formula multiplier = F.Id("M"), band = F.Id("B");
        Formula scale = F.Id("L"), safe = F.Id("a"), depth = F.Id("b");
        Formula f = F.Id("f"), xi = F.Id("xi"), ratio = F.Id("ratio");
        Formula ratios = F.Id("concentrationRatios");
        Formula concentration = F.Id("concentration");
        Formula quadratic = F.Id("quadraticForm");
        Formula setReal = Call("Set", real);
        Formula factor = Call("div", D(1), Call("mul", D(2), Call("pi")));

        Formula Supported(Formula value) => ApplyTwo(supported, scale, value);
        Formula Mass(Formula value) => Apply(mass, value);
        Formula Density(Formula value, Formula frequency) =>
            ApplyTwo(density, value, frequency);
        Formula Multiplier(Formula frequency) => Apply(multiplier, frequency);
        Formula BandMass(Formula value) => Call(
            "mul",
            factor,
            Call("integralOn", band,
                Lambda("xi", real, Density(value, xi))));
        Formula TotalMass(Formula value) => Call(
            "mul",
            factor,
            Call("integral", real,
                Lambda("xi", real, Density(value, xi))));
        Formula Quadratic(Formula value) => Apply(quadratic, value);

        Formula ratioPredicate = Exists(
            [Bound("f", test)],
            All(
                NotEqual(f, D(0)),
                Supported(f),
                Equal(ratio, Call("div", BandMass(f), Mass(f)))));
        Formula ratioSet = new Formula.SetBuilder(ratioPredicate, ratio, real);
        Formula weightedIntegrand = Lambda(
            "xi", real, Call("mul", Multiplier(xi), Density(f, xi)));

        Formula outsideLower = ForAll(
            [Bound("xi", real)],
            Implies(
                new Formula.Not(new Formula.Relation(
                    xi, FormulaRelationOperator.MemberOf, band)),
                AtMost(safe, Multiplier(xi))));
        Formula insideLower = ForAll(
            [Bound("xi", real)],
            Implies(
                new Formula.Relation(xi, FormulaRelationOperator.MemberOf, band),
                AtMost(Call("neg", depth), Multiplier(xi))));
        Formula densityIntegrable = ForAll(
            [Bound("f", test)], Call("Integrable", Apply(density, f)));
        Formula weightedIntegrable = ForAll(
            [Bound("f", test)], Call("Integrable", weightedIntegrand));
        Formula densityNonnegative = ForAll(
            [Bound("f", test), Bound("xi", real)],
            AtMost(D(0), Density(f, xi)));
        Formula plancherel = ForAll(
            [Bound("f", test)], Equal(TotalMass(f), Mass(f)));
        Formula zeroDensity = ForAll(
            [Bound("xi", real)], Equal(Density(D(0), xi), D(0)));
        Formula positiveMass = ForAll(
            [Bound("f", test)],
            Implies(NotEqual(f, D(0)), Less(D(0), Mass(f))));

        Formula assumptions = All(
            Call("Zero", test),
            Call("MeasurableSet", band),
            Less(D(0), safe),
            AtMost(D(0), depth),
            outsideLower,
            insideLower,
            densityIntegrable,
            weightedIntegrable,
            densityNonnegative,
            plancherel,
            zeroDensity,
            positiveMass);

        Formula gap = Call(
            "sub", safe,
            Call("mul", Call("add", safe, depth), concentration));
        Formula lowerClause = ForAll(
            [Bound("f", test)],
            Implies(
                Supported(f),
                AtMost(Call("mul", gap, Mass(f)), Quadratic(f))));
        Formula strictClause = Implies(
            Less(concentration, Call("div", safe, Call("add", safe, depth))),
            ForAll(
                [Bound("f", test)],
                Implies(
                    And(NotEqual(f, D(0)), Supported(f)),
                    Less(D(0), Quadratic(f)))));
        Formula definitions = Seq(
            Let("concentrationRatios", ratioSet),
            Let("concentration", Call("sSup", ratios)),
            Let("quadraticForm", Lambda(
                "f", test,
                Call("mul", factor,
                    Call("integral", real, weightedIntegrand)))),
            And(lowerClause, strictClause));

        return F.Disp(ForAll(
            [
                Bound("Test", type),
                Bound("supportedIn", new Formula.TypeArrow(
                    real, new Formula.TypeArrow(test, prop))),
                Bound("spatialMass", new Formula.TypeArrow(test, real)),
                Bound("spectralDensity", new Formula.TypeArrow(
                    test, new Formula.TypeArrow(real, real))),
                Bound("M", new Formula.TypeArrow(real, real)),
                Bound("B", setReal),
                Bound("L", real),
                Bound("a", real),
                Bound("b", real),
            ],
            Implies(assumptions, definitions)));
    }
}
