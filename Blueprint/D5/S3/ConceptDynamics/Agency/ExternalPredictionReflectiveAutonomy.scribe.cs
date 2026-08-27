using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Agency;

internal sealed class ExternalPredictionReflectiveAutonomyDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Agency/ExternalPredictionReflectiveAutonomy."
            + "external_prediction_compatible_with_reflective_autonomy";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Refinement constructs an external action predictor, and such predictability "
            + "coexists with reflective autonomy.",
        H("External Prediction and Reflective Autonomy"),
        Blocks(Describe.Lean(
            DescribeId.Create("external-prediction-reflective-autonomy"),
            DeclarationHandle.Create(Declaration),
            H("External prediction is compatible with reflective autonomy"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "When the reason readout R factors through an external readout E by p, "
                        + "the action policy pi factors through E by the constructed predictor "
                        + "pi composed with p.")),
                Paragraph(Text(
                    "The second public clause is a shared Boolean model. Its same reason, "
                        + "external readout, factor, policy, and action witness both internal "
                        + "control and external prediction.")),
                Paragraph(Text(
                    "That model also makes the selected action available, approved before "
                        + "reflection, unchanged by reflection, and approved afterwards. Thus "
                        + "predictability alone does not negate reflective autonomy."))),
            DescribeRole.Theorem))));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Compose(Formula outer, Formula inner) =>
        Seq(outer, Sp, Circ, Sp, inner);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(clauses[index], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula reasonValue = F.Id("Reason");
        Formula externalValue = F.Id("External");
        Formula actionValue = F.Id("U");
        Formula reason = F.Id("R");
        Formula external = F.Id("E");
        Formula policy = F.Id("pi");
        Formula factor = F.Id("p");
        Formula generalFactor = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("p", Arrow(externalValue, reasonValue))],
            And(
                Equal(reason, Compose(factor, external)),
                Equal(
                    Compose(policy, reason),
                    Compose(Compose(policy, factor), external))));
        Formula generalClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", TypeUniverse()),
                Bound("Reason", TypeUniverse()),
                Bound("External", TypeUniverse()),
                Bound("U", TypeUniverse()),
                Bound("R", Arrow(state, reasonValue)),
                Bound("E", Arrow(state, externalValue)),
                Bound("pi", Arrow(reasonValue, actionValue)),
            ],
            Implies(Call("Refines", reason, external), generalFactor));

        Formula boolean = F.Id("Bool");
        Formula action = F.Id("A");
        Formula available = F.Id("Available");
        Formula approves = F.Id("V");
        Formula reflect = F.Id("rho");
        Formula actual = F.Id("x");
        Formula actualAction = Apply(action, actual);
        Formula reflected = Apply(reflect, actual);
        Formula coexistenceBody = And(
            Equal(reason, Compose(factor, external)),
            Equal(action, Compose(policy, reason)),
            Equal(action, Compose(Compose(policy, factor), external)),
            Seq(actualAction, Sp, InMacro, Sp, Apply(available, actual)),
            Apply(approves, actual, actualAction),
            Equal(Apply(action, reflected), actualAction),
            Apply(approves, reflected, actualAction));
        Formula coexistence = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                Bound("R", Arrow(boolean, boolean)),
                Bound("E", Arrow(boolean, boolean)),
                Bound("p", Arrow(boolean, boolean)),
                Bound("pi", Arrow(boolean, boolean)),
                Bound("A", Arrow(boolean, boolean)),
                Bound("Available", Arrow(boolean, Call("Set", boolean))),
                Bound("V", Arrow(boolean, Arrow(boolean, F.Id("Prop")))),
                Bound("rho", Arrow(boolean, boolean)),
                Bound("x", boolean),
            ],
            coexistenceBody);

        return Disp(And(generalClause, coexistence));
    }
}
