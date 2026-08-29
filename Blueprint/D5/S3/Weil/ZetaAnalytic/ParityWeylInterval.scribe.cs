using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaAnalytic;

internal sealed class ParityWeylIntervalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZetaAnalytic/ParityWeylInterval.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The affine even and odd channels determine a coordinate-independent resolvent "
            + "interval and its positive spectral completions.",
        H("Parity Weyl Interval"),
        Blocks(Describe.Lean(
            DescribeId.Create("parity-weyl-interval"),
            DeclarationHandle.Create(Prefix + "parity_weyl_interval"),
            H("Parity Weyl interval"),
            StatementSource.FromAuthor(IntervalFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The proof treats zero boundary channels by the two kernel hypotheses. "
                    + "For nonzero channels, conditional-completeness bounds turn affine "
                    + "positivity into the lower and upper Rayleigh endpoint inequalities. "
                    + "Direct ring identities prove invariance under recentering."))),
            DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, Formula value) =>
        Call("apply", function, value);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Greater(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThan, right);

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

    private static Formula Let(string name, Formula value) =>
        Seq(Operatorname, Grp(F.Id("let")), Sp, F.Id(name), Sp, Eq, Sp, value, Comma, Sp);

    private static Formula Lambda(string name, Formula domain, Formula body) =>
        Seq(F.Id(name), Colon, Sp, domain, Sp, Mapsto, Sp, body);

    private static Formula IntervalFormula()
    {
        Formula type = F.Id("Type"), real = Call("Real");
        Formula even = F.Id("Even"), odd = F.Id("Odd"), sourceType = F.Id("Source");
        Formula measureReal = Call("Measure", real);
        Formula evenBase = F.Id("evenBase"), evenBoundary = F.Id("evenBoundary");
        Formula oddBase = F.Id("oddBase"), oddBoundary = F.Id("oddBoundary");
        Formula reference = F.Id("referenceBudget"), source = F.Id("source");
        Formula spectralReading = F.Id("spectralReading");
        Formula resolventMoment = F.Id("resolventMoment");
        Formula e = F.Id("e"), o = F.Id("o"), q = F.Id("q"), r = F.Id("R");
        Formula delta = F.Id("delta"), nu = F.Id("nu"), x = F.Id("x");
        Formula evenRatios = F.Id("evenRatios"), oddRatios = F.Id("oddRatios");
        Formula lower = F.Id("lower"), upper = F.Id("upper");
        Formula admissible = F.Id("admissible");
        Formula shiftedAdmissible = F.Id("shiftedAdmissible");
        Formula completion = F.Id("completion");

        Formula evenRatioPredicate = Exists(
            [Bound("e", even)],
            And(
                NotEqual(Apply(evenBoundary, e), D(0)),
                Equal(q, Call("div", Call("neg", Apply(evenBase, e)),
                    Apply(evenBoundary, e)))));
        Formula oddRatioPredicate = Exists(
            [Bound("o", odd)],
            And(
                NotEqual(Apply(oddBoundary, o), D(0)),
                Equal(q, Call("div", Apply(oddBase, o), Apply(oddBoundary, o)))));
        Formula evenRatioSet = new Formula.SetBuilder(evenRatioPredicate, q, real);
        Formula oddRatioSet = new Formula.SetBuilder(oddRatioPredicate, q, real);

        Formula evenAt = Call("add", Apply(evenBase, e),
            Call("mul", Call("sub", r, reference), Apply(evenBoundary, e)));
        Formula oddAt = Call("sub", Apply(oddBase, o),
            Call("mul", Call("sub", r, reference), Apply(oddBoundary, o)));
        Formula admissibleBody = All(
            AtMost(D(0), r),
            ForAll([Bound("e", even)], AtMost(D(0), evenAt)),
            ForAll([Bound("o", odd)], AtMost(D(0), oddAt)));

        Formula shiftedEvenAt = Call("add",
            Call("add", Apply(evenBase, e),
                Call("mul", delta, Apply(evenBoundary, e))),
            Call("mul", Call("sub", r, Call("add", reference, delta)),
                Apply(evenBoundary, e)));
        Formula shiftedOddAt = Call("sub",
            Call("sub", Apply(oddBase, o),
                Call("mul", delta, Apply(oddBoundary, o))),
            Call("mul", Call("sub", r, Call("add", reference, delta)),
                Apply(oddBoundary, o)));
        Formula shiftedBody = All(
            AtMost(D(0), r),
            ForAll([Bound("e", even)], AtMost(D(0), shiftedEvenAt)),
            ForAll([Bound("o", odd)], AtMost(D(0), shiftedOddAt)));

        Formula reflection = Equal(
            Call("map", Seq(Open, Lambda("x", real, Call("neg", x)), Close), nu), nu);
        Formula completionBody = Exists(
            [Bound("nu", measureReal)],
            All(
                reflection,
                Equal(Apply(spectralReading, nu), source),
                Equal(Apply(resolventMoment, nu), r)));
        Formula interval = Call("Icc", Call("max", D(0), lower), upper);
        Formula intervalMembership =
            new Formula.Relation(r, FormulaRelationOperator.MemberOf, interval);

        Formula characterization = ForAll(
            [Bound("R", real)], Iff(Apply(admissible, r), intervalMembership));
        Formula infeasibility = Implies(
            Greater(lower, upper),
            new Formula.Not(Exists([Bound("R", real)], Apply(admissible, r))));
        Formula shiftedSet = new Formula.SetBuilder(
            Call("applyTwo", shiftedAdmissible, delta, r), r, real);
        Formula admissibleSet = new Formula.SetBuilder(Apply(admissible, r), r, real);
        Formula invariance = ForAll(
            [Bound("delta", real)], Equal(shiftedSet, admissibleSet));

        Formula completionOfPositive = ForAll(
            [Bound("R", real)],
            Implies(Apply(admissible, r), Apply(completion, r)));
        Formula positiveOfCompletion = ForAll(
            [Bound("nu", measureReal)],
            Implies(
                reflection,
                Implies(
                    Equal(Apply(spectralReading, nu), source),
                    Apply(admissible, Apply(resolventMoment, nu)))));
        Formula completionEquivalence = Implies(
            And(completionOfPositive, positiveOfCompletion),
            ForAll(
                [Bound("R", real)],
                Iff(intervalMembership, Apply(completion, r))));

        Formula assumptions = All(
            ForAll([Bound("e", even)], AtMost(D(0), Apply(evenBoundary, e))),
            ForAll([Bound("o", odd)], AtMost(D(0), Apply(oddBoundary, o))),
            ForAll(
                [Bound("e", even)],
                Implies(
                    Equal(Apply(evenBoundary, e), D(0)),
                    AtMost(D(0), Apply(evenBase, e)))),
            ForAll(
                [Bound("o", odd)],
                Implies(
                    Equal(Apply(oddBoundary, o), D(0)),
                    AtMost(D(0), Apply(oddBase, o)))),
            Exists([Bound("e", even)], NotEqual(Apply(evenBoundary, e), D(0))),
            Exists([Bound("o", odd)], NotEqual(Apply(oddBoundary, o), D(0))),
            Call("BddAbove", evenRatioSet),
            Call("BddBelow", oddRatioSet));

        Formula definitions = Seq(
            Let("evenRatios", evenRatioSet),
            Let("oddRatios", oddRatioSet),
            Let("lower", Call("add", reference, Call("sSup", evenRatios))),
            Let("upper", Call("add", reference, Call("sInf", oddRatios))),
            Let("admissible", Lambda("R", real, admissibleBody)),
            Let("shiftedAdmissible", Lambda(
                "delta", real, Lambda("R", real, shiftedBody))),
            Let("completion", Lambda("R", real, completionBody)),
            All(characterization, infeasibility, invariance, completionEquivalence));

        return F.Disp(ForAll(
            [
                Bound("Even", type),
                Bound("Odd", type),
                Bound("Source", type),
                Bound("evenBase", new Formula.TypeArrow(even, real)),
                Bound("evenBoundary", new Formula.TypeArrow(even, real)),
                Bound("oddBase", new Formula.TypeArrow(odd, real)),
                Bound("oddBoundary", new Formula.TypeArrow(odd, real)),
                Bound("referenceBudget", real),
                Bound("source", sourceType),
                Bound("spectralReading", new Formula.TypeArrow(measureReal, sourceType)),
                Bound("resolventMoment", new Formula.TypeArrow(measureReal, real)),
            ],
            Implies(assumptions, definitions)));
    }
}
