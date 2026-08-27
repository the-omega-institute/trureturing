using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InterventionsExchange;

internal sealed class FiniteInterventionSequenceCommutationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/InterventionsExchange/FiniteInterventionSequenceCommutation."
            + "finite_intervention_sequences_commute";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One-step commuting intervention squares commute along every finite action list.",
        H("Finite Intervention Sequence Commutation"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-intervention-sequences-commute"),
            DeclarationHandle.Create(Declaration),
            H("Atomic commuting squares preserve every finite intervention path"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The micro and macro action families act on their respective source and "
                        + "abstract carriers. Each action makes the abstraction square commute.")),
                Paragraph(Text(
                    "Both finite sequence maps are the public left folds of those action "
                        + "families. List induction transports the atomic equation through the "
                        + "remaining macro fold, yielding the displayed composite-map equality."))),
            DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula FoldedAction(
        Formula actions,
        Formula actionMap,
        Formula state,
        Formula action)
    {
        Formula folder = Seq(
            Open, state, Comma, Sp, action, Sp, Mapsto, Sp,
            Apply(Apply(actionMap, action), state), Close);
        return Seq(
            Open, state, Sp, Mapsto, Sp,
            Call("foldl", folder, state, actions), Close);
    }

    private static Formula Compose(Formula outer, Formula inner) =>
        Seq(outer, Sp, Circ, Sp, inner);

    private static Formula TheoremFormula()
    {
        Formula actionType = F.Id("U");
        Formula microType = F.Id("X");
        Formula macroType = F.Id("Z");
        Formula abstraction = F.Id("C");
        Formula micro = F.Id("F");
        Formula macro = F.Id("G");
        Formula action = F.Id("u");
        Formula actions = F.Id("alpha");
        Formula microState = F.Id("x");
        Formula macroState = F.Id("z");

        Formula atomicCommutation = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("u", actionType), Bound("x", microType)],
            EqualTo(
                Apply(abstraction, Apply(Apply(micro, action), microState)),
                Apply(Apply(macro, action), Apply(abstraction, microState))));

        Formula finiteCommutation = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("alpha", Call("List", actionType))],
            EqualTo(
                Compose(
                    abstraction,
                    FoldedAction(actions, micro, microState, action)),
                Compose(
                    FoldedAction(actions, macro, macroState, action),
                    abstraction)));

        Formula theorem = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("U", F.Id("Type")),
                Bound("X", F.Id("Type")),
                Bound("Z", F.Id("Type")),
                Bound("C", Arrow(microType, macroType)),
                Bound("F", Arrow(actionType, Arrow(microType, microType))),
                Bound("G", Arrow(actionType, Arrow(macroType, macroType))),
            ],
            Implies(atomicCommutation, finiteCommutation));

        return Disp(theorem);
    }
}
