using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Interventions;

internal sealed class PredictiveClosureInterventionSeparationDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A naturally descending update need not make every intervention descend.",
        H("Predictive Closure Does Not Imply Intervention Closure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("predictive-closure-does-not-imply-intervention-closure"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Interventions/"
                        + "PredictiveClosureInterventionSeparation."
                        + "predictive_closure_not_intervention_closure"),
                H("Predictive closure does not imply intervention closure"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The witness uses one interface and a family of two updates. The false "
                            + "action is exactly the natural update, and that update descends "
                            + "through the interface.")),
                    Paragraph(Text(
                        "The true action separates two states in the same interface fiber. Hence "
                            + "the shared action family is not closed under the interface even "
                            + "though its distinguished natural update is closed."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula state = Call("Fin", F.D(3));
        Formula boolean = F.Id("Bool");
        Formula readout = F.Id("q");
        Formula natural = F.Id("F");
        Formula action = F.Id("Fa");
        Formula actionIndex = F.Id("a");
        Formula left = F.Id("x");
        Formula right = F.Id("y");

        Formula actionExtendsNatural = Equal(
            Apply(action, F.Id("false")),
            natural);
        Formula naturalDescent = Descent(readout, natural);
        Formula notAllActionsDescend = new Formula.Not(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("a", boolean)],
            Descent(readout, Apply(action, actionIndex))));
        Formula kernelViolation = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                Bound("a", boolean),
                Bound("x", state),
                Bound("y", state),
            ],
            And(
                Equal(Apply(readout, left), Apply(readout, right)),
                NotEqual(
                    Apply(readout, Apply(action, actionIndex, left)),
                    Apply(readout, Apply(action, actionIndex, right)))));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                Bound("q", Arrow(state, boolean)),
                Bound("F", Arrow(state, state)),
                Bound("Fa", Arrow(boolean, Arrow(state, state))),
            ],
            And(
                actionExtendsNatural,
                And(
                    naturalDescent,
                    And(notAllActionsDescend, kernelViolation)))));
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Descent(Formula readout, Formula update) =>
        Call("EffectiveDescent", readout, update);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
