using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Agency;

internal sealed class DeterministicSafePolicyExistenceDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Agency/DeterministicSafePolicyExistence."
            + "deterministic_safe_policy_exists_iff";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fiberwise common legal actions characterize deterministic observation-based safe policies.",
        H("Deterministic Safe Policy Existence"),
        Blocks(Describe.Lean(
            DescribeId.Create("deterministic-safe-policy-exists-exactly-on-nonempty-safe-fibers"),
            DeclarationHandle.Create(Declaration),
            H("A safe deterministic policy exists exactly when every effective fiber is safe"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The policy is defined on the realized observation range. Safety requires its "
                        + "chosen action to be legal at every full state compatible with that "
                        + "observation.")),
                Paragraph(Text(
                    "Such a policy supplies a common legal action in each effective fiber. "
                        + "Conversely, set-theoretic choice assembles one common action from every "
                        + "effective fiber; no measurable-selector claim is made."))),
            DescribeRole.Theorem))));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula TheoremFormula()
    {
        Formula fullStateType = F.Id("X");
        Formula observationType = F.Id("Q");
        Formula actionType = F.Id("A");
        Formula observation = F.Id("q");
        Formula legal = F.Id("Legal");
        Formula policy = F.Id("s");
        Formula fiber = F.Id("z");
        Formula fullState = F.Id("x");
        Formula action = F.Id("a");
        Formula effectiveCarrier = Call("range", observation);
        Formula compatibility = Equal(
            Apply(observation, fullState), Call("val", fiber));
        Formula policySafety = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("z", effectiveCarrier), Bound("x", fullStateType)],
            Implies(
                compatibility,
                Apply(legal, fullState, Apply(policy, fiber))));
        Formula safePolicy = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("s", Arrow(effectiveCarrier, actionType))],
            policySafety);
        Formula commonAction = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("a", actionType)],
            new Formula.BindMany(
                FormulaQuantifier.ForAll,
                [Bound("x", fullStateType)],
                Implies(compatibility, Apply(legal, fullState, action))));
        Formula everyFiberSafe = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("z", effectiveCarrier)],
            commonAction);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", TypeUniverse()),
                Bound("Q", TypeUniverse()),
                Bound("A", TypeUniverse()),
                Bound("q", Arrow(fullStateType, observationType)),
                Bound("Legal", Arrow(fullStateType, Arrow(actionType, F.Id("Prop")))),
            ],
            new Formula.Logic(safePolicy, FormulaLogicOperator.Iff, everyFiberSafe)));
    }
}
