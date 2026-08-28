using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class SafeComplementFiniteIndexDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/ZetaBridge/SafeComplementFiniteIndex.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A concentration-controlled spectral complement has a strict Weil gap and finite negative index.",
        H("Safe Complement Gap and Finite Negative Index"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("safe-complement-gap"),
                DeclarationHandle.Create(Prefix + "safe_complement_gap"),
                H("Safe-complement gap"),
                StatementSource.FromAuthor(SafeGapFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On the canonical Weil-test carrier, concentration in the dangerous "
                        + "multiplier band and pole orthogonality give the displayed positive "
                        + "gap for the frozen zero-side quadratic form."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-negative-index-bound"),
                DeclarationHandle.Create(Prefix + "finite_negative_index_bound"),
                H("Finite negative-index bound"),
                StatementSource.FromAuthor(FiniteIndexFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A strictly positive complementary subspace prevents a negative "
                        + "subspace from having dimension larger than the retained summand."))),
                DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }

    private static Formula SafeGapFormula()
    {
        Formula type = F.Id("Type");
        Formula real = Call("Real");
        Formula prop = Call("Prop");
        Formula zeroData = Call("ZeroData");
        Formula testType = Call("WeilTestFunction");
        Formula z = F.Id("Z"), scale = F.Id("L"), threshold = F.Id("a");
        Formula eta = F.Id("eta"), predicate = F.Id("Q"), test = F.Id("f");
        Formula xi = F.Id("xi"), x = F.Id("x"), g = F.Id("g");
        Formula multiplier = Call("fixedScaleMultiplier", scale, xi);
        Formula dangerous = Call("setOf",
            Call("lambda", Call("typed", xi, real), Less(multiplier, threshold)));
        Formula depth = Call("max", D(0), Call("neg", Call("sInf",
            Call("image", Call("fixedScaleMultiplier", scale), dangerous))));
        Formula delta = Call("sub", threshold,
            Call("mul", Call("add", threshold, depth), eta));
        Formula transformEnergy(Formula value, Formula frequency) =>
            Call("normSq", Call("fourierLaplace", value, frequency));
        Formula bandMass(Formula value) => Call("mul",
            Call("div", D(1), Call("mul", D(2), Call("pi"))),
            Call("integralOn", dangerous,
                Call("lambda", Call("typed", xi, real), transformEnergy(value, xi))));
        Formula pole(Formula value) => Call("integral", real,
            Call("lambda", Call("typed", x, real),
                Call("mul", Call("cosh", Call("div", x, D(2))),
                Call("apply", value, x))));
        Formula zeroSide = Call("realPart",
            Call("zeroSum", z, Call("convolutionSquare", test)));

        Formula concentration = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("g", testType)],
            Implies(Call("apply", predicate, g),
                AtMost(bandMass(g), Call("mul", eta, Call("l2Mass", g)))));
        Formula poleOrthogonality = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("g", testType)],
            Implies(Call("apply", predicate, g), Equal(pole(g), D(0))));

        Formula assumptions = All(
            Call("apply", predicate, test),
            new Formula.Relation(
                Call("tsupport", test), FormulaRelationOperator.SubsetOf,
                Call("Icc", Call("neg", scale), scale)),
            Call("SymmetricConvergent", z, Call("convolutionSquare", test)),
            Call("ArchimedeanConvergent", Call("convolutionSquare", test)),
            Call("Integrable", Call("lambda", Call("typed", xi, real),
                Call("mul", multiplier, transformEnergy(test, xi)))),
            Call("MeasurableSet", dangerous),
            Call("BddBelow", Call("image", Call("fixedScaleMultiplier", scale), dangerous)),
            Less(D(0), threshold),
            Less(D(0), eta),
            Less(eta, Call("div", threshold, Call("add", threshold, depth))),
            concentration,
            poleOrthogonality);
        Formula conclusion = And(
            Less(D(0), delta),
            AtMost(Call("mul", delta, Call("l2Mass", test)), zeroSide));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Z", zeroData),
                Bound("L", real),
                Bound("a", real),
                Bound("eta", real),
                Bound("Q", Call("Function", testType, prop)),
                Bound("f", testType),
            ],
            Implies(assumptions, conclusion)));
    }

    private static Formula FiniteIndexFormula()
    {
        Formula type = F.Id("Type");
        Formula real = Call("Real");
        Formula prop = Call("Prop");
        Formula space = F.Id("H"), energy = F.Id("energy");
        Formula retained = F.Id("P"), complement = F.Id("Q");
        Formula delta = F.Id("delta"), q = F.Id("q");
        Formula submodule = Call("Submodule", real, space);
        Formula safe = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("q", space)],
            Implies(
                new Formula.Relation(q, FormulaRelationOperator.MemberOf, complement),
                AtMost(
                    Call("mul", delta, Call("pow", Call("norm", q), D(2))),
                    Call("apply", energy, q))));
        Formula assumptions = All(
            Call("NormedAddCommGroup", space),
            Call("InnerProductSpace", real, space),
            Call("FiniteDimensional", real, retained),
            Call("IsCompl", retained, complement),
            Less(D(0), delta),
            safe);
        Formula conclusion = AtMost(
            Call("negativeIndex", energy),
            Call("withTop", Call("finrank", real, retained)));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("H", type),
                Bound("energy", Call("Function", space, real)),
                Bound("P", submodule),
                Bound("Q", submodule),
                Bound("delta", real),
            ],
            Implies(assumptions, conclusion)));
    }
}
