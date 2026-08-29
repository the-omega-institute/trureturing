using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class ActiveFiniteContactCompletionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/TestFunctions/ActiveFiniteContactCompletion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive active pressure produces an exact finite-contact completion.",
        H("Active Finite-Contact Completion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("active-finite-contact-completion"),
                DeclarationHandle.Create(Prefix + "active_finite_contact_completion"),
                H("Active pressure gives a finite atomic completion"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A finite residual supported on the active KKT contact set can be "
                            + "replaced by positive contact atoms while retaining its mass "
                            + "and every moment in the supplied real observer family.")),
                    Paragraph(Text(
                        "The completion keeps the same nonnegative Haar coefficient, uses at "
                            + "most d plus one atoms, and every chosen contact has an inverse "
                            + "contact, so the support is indexed by at most d plus one "
                            + "conjugate contact orbits."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula natural = Call("Nat");
        Formula real = Call("Real");
        Formula complex = Call("Complex");
        Formula nonnegativeReal = Call("NNReal");
        Formula circle = Call("Circle");
        Formula test = Call("WeilTestFunction");
        Formula d = F.Id("d"), a = F.Id("a"), theta = F.Id("theta");
        Formula alpha = F.Id("alpha"), phi = F.Id("phi");
        Formula observer = F.Id("observer"), sigma = F.Id("sigma");
        Formula indexType = F.Id("I"), finiteIndex = F.Id("finiteI");
        Formula point = F.Id("point"), weight = F.Id("weight");
        Formula completion = F.Id("muStar");
        Formula i = F.Id("i"), x = F.Id("x"), r = F.Id("r"), z = F.Id("z");
        Formula observerIndex = Call("Fin", d);

        Formula Moment(Formula testFunction, Formula circlePoint) =>
            Call("cayleyMomentFunction", a, testFunction, circlePoint);
        Formula ObserverAt(Formula observerIndexValue) =>
            Apply(observer, observerIndexValue);
        Formula PointAt(Formula atomIndex) => Apply(point, atomIndex);
        Formula WeightAt(Formula atomIndex) => Apply(weight, atomIndex);
        Formula Contact(Formula circlePoint) =>
            Equal(Add(Moment(phi, circlePoint), theta), D(0));

        Formula atomicResidual = Call(
            "sum",
            r,
            indexType,
            Call(
                "smul",
                Call("ofReal", WeightAt(r)),
                Call("dirac", PointAt(r))));
        Formula completionMeasure = Add(
            Call("smul", alpha, Call("normalizedCircleHaar")),
            atomicResidual);
        Formula contactSet = new Formula.SetBuilder(Contact(z), z, circle);

        Formula assumptions = All(
            Less(D(0), a),
            Less(D(0), theta),
            ForAll(
                [Bound("i", observerIndex), Bound("x", real)],
                Equal(
                    Call("conj", Apply(ObserverAt(i), x)),
                    Apply(ObserverAt(i), x))),
            new Formula.Relation(
                Call("support", sigma),
                FormulaRelationOperator.SubsetOf,
                contactSet));

        Formula residualMass = Equal(
            Call("sum", r, indexType, WeightAt(r)),
            Call("measureReal", sigma, Call("univ", circle)));
        Formula momentPreservation = ForAll(
            [Bound("i", observerIndex)],
            Equal(
                Call(
                    "integral",
                    z,
                    circle,
                    Moment(ObserverAt(i), z),
                    atomicResidual),
                Call(
                    "integral",
                    z,
                    circle,
                    Moment(ObserverAt(i), z),
                    sigma)));
        Formula conclusion = Exists(
            [
                Bound("I", type),
                Bound("finiteI", Call("Fintype", indexType)),
                Bound("point", new Formula.TypeArrow(indexType, circle)),
                Bound("weight", new Formula.TypeArrow(indexType, real)),
                Bound("muStar", Call("Measure", circle))
            ],
            All(
                AtMost(Call("card", indexType), Add(d, D(1))),
                ForAll([Bound("r", indexType)], Less(D(0), WeightAt(r))),
                ForAll([Bound("r", indexType)], Contact(PointAt(r))),
                ForAll(
                    [Bound("r", indexType)],
                    Contact(Call("inv", PointAt(r)))),
                residualMass,
                Equal(completion, completionMeasure),
                momentPreservation));

        return Disp(ForAll(
            [
                Bound("d", natural),
                Bound("a", real),
                Bound("theta", real),
                Bound("alpha", nonnegativeReal),
                Bound("phi", test),
                Bound("observer", new Formula.TypeArrow(observerIndex, test)),
                Bound("sigma", Call("FiniteMeasure", circle))
            ],
            Implies(assumptions, conclusion)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
}
