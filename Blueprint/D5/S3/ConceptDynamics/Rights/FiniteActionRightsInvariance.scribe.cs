using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Rights;

internal sealed class FiniteActionRightsInvarianceDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Rights/FiniteActionRightsInvariance."
            + "finite_action_sequence_preserves_rights";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite sequence of certified atomic actions preserves the safe state set.",
        H("Finite Action Rights Invariance"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-action-sequences-preserve-rights"),
            DeclarationHandle.Create(Declaration),
            H("Certified atomic actions generate finite safe processes"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Let each action in a family map a designated safe set into itself. Folding any "
                    + "finite action list from left to right then maps every initially safe state "
                    + "back into the same safe set. The empty list is the identity case, and the "
                    + "inductive step applies the next atomic certificate before the remaining "
                    + "list certificate."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula actionType = F.Id("U");
        Formula safe = F.Id("S");
        Formula act = F.Id("F");
        Formula action = F.Id("u");
        Formula actions = F.Id("actions");
        Formula state = F.Id("x");
        Formula setOfStates = Call("Set", stateType);
        Formula actionMap = Arrow(actionType, Arrow(stateType, stateType));
        Formula atomicPreservation = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("u"),
            actionType,
            Call("MapsTo", Apply(act, action), safe, safe));
        Formula folder = F.Seq(
            F.Open, state, F.Comma, F.Sp, action, F.Sp, F.Mapsto, F.Sp,
            Apply(Apply(act, action), state), F.Close);
        Formula foldedAction = F.Seq(
            F.Open, state, F.Sp, F.Mapsto, F.Sp,
            Call("foldl", folder, state, actions), F.Close);
        Formula finitePreservation = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("actions"),
            Call("List", actionType),
            Call("MapsTo", foldedAction, safe, safe));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", F.Id("Type")),
                Bound("U", F.Id("Type")),
                Bound("S", setOfStates),
                Bound("F", actionMap),
            ],
            Implies(atomicPreservation, finitePreservation)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);
}
