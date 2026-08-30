using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Agency;

internal sealed class BoundaryRelativeAgencyDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Agency/BoundaryRelativeAgency.boundary_relative_agency";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A past-choice-updated decision variable is internal or external relative to observer access.",
        H("Boundary-Relative Agency"),
        Blocks(Describe.Lean(
            DescribeId.Create("boundary-relative-agency"),
            DeclarationHandle.Create(Declaration),
            H("Observer access determines the control boundary"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The decision process is constructed by applying the update map to the "
                        + "recorded past choice. The displayed control premise says that this "
                        + "same decision process determines action.")),
                Paragraph(Text(
                    "When the observer interface recovers the decision process, composition "
                        + "recovers action from the observer interface as well. This is the "
                        + "internal-reason side of the boundary.")),
                Paragraph(Text(
                    "On the external side, one shared pair has equal observer readouts but "
                        + "different decision and action values. It witnesses observer "
                        + "inaccessibility and rules out descent of action to that boundary."))),
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

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula TheoremFormula()
    {
        Formula history = F.Id("H");
        Formula observerState = F.Id("O");
        Formula pastChoiceType = F.Id("C");
        Formula decisionType = F.Id("D");
        Formula actionType = F.Id("A");
        Formula observer = F.Id("o");
        Formula pastChoice = F.Id("c");
        Formula update = F.Id("u");
        Formula action = F.Id("a");
        Formula decision = Compose(update, pastChoice);
        Formula control = Call("ControlPrinciple", decision, action);
        Formula internalClause = Implies(
            Call("ControlPrinciple", observer, decision),
            Call("ControlPrinciple", observer, action));

        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula externalConclusion = And(
            Call("MoralLuckWitness", observer, decision),
            Seq(Neg, Sp, Call("ControlPrinciple", observer, action)));
        Formula externalClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("x", history), Bound("y", history)],
            Implies(
                Equal(Apply(observer, left), Apply(observer, right)),
                Implies(
                    NotEqual(
                        Apply(update, Apply(pastChoice, left)),
                        Apply(update, Apply(pastChoice, right))),
                    Implies(
                        NotEqual(Apply(action, left), Apply(action, right)),
                        externalConclusion))));

        Formula body = Implies(control, And(internalClause, externalClause));
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("H", TypeUniverse()),
                Bound("O", TypeUniverse()),
                Bound("C", TypeUniverse()),
                Bound("D", TypeUniverse()),
                Bound("A", TypeUniverse()),
                Bound("o", Arrow(history, observerState)),
                Bound("c", Arrow(history, pastChoiceType)),
                Bound("u", Arrow(pastChoiceType, decisionType)),
                Bound("a", Arrow(history, actionType)),
            ],
            body));
    }
}
