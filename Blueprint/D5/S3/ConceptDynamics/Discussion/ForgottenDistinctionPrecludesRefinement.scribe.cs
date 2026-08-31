using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Discussion;

internal sealed class ForgottenDistinctionPrecludesRefinementDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Discussion/ForgottenDistinctionPrecludesRefinement."
            + "forgotten_distinction_precludes_refinement";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A future readout that forgets a past distinction cannot refine the past readout.",
        H("Forgotten Distinction Precludes Refinement"),
        Blocks(Describe.Lean(
            DescribeId.Create("forgotten-distinction-precludes-refinement"),
            DeclarationHandle.Create(Declaration),
            H("Forgetting a distinction obstructs refinement"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The past and future concepts are arbitrary readouts on the same state "
                        + "space. Two states have different past readouts but the same future "
                        + "readout, which directly records that the old distinction was lost.")),
                Paragraph(Text(
                    "If the future refined the past, the canonical refinement factor would "
                        + "transport equality of the future readouts back to equality of the "
                        + "past readouts, contradicting the displayed distinction.")),
                Paragraph(Text(
                    "The proof imports the existing refinement-preservation theorem and takes "
                        + "its contrapositive. No new concept or refinement relation is defined."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula universe = F.Id("Type");
        Formula stateType = F.Id("X");
        Formula pastType = F.Id("C");
        Formula futureType = F.Id("D");
        Formula past = F.Id("past");
        Formula future = F.Id("future");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula oldDistinction = new Formula.Relation(
            Apply(past, left), FormulaRelationOperator.NotEqual, Apply(past, right));
        Formula forgotten = new Formula.Relation(
            Apply(future, left), FormulaRelationOperator.Equal, Apply(future, right));
        Formula premises = new Formula.Logic(
            oldDistinction, FormulaLogicOperator.And, forgotten);
        Formula conclusion = new Formula.Not(Call("Refines", past, future));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", universe),
                Bound("C", universe),
                Bound("D", universe),
                Bound("past", Call("Concept", stateType, pastType)),
                Bound("future", Call("Concept", stateType, futureType)),
                Bound("x", stateType),
                Bound("y", stateType),
            ],
            new Formula.Logic(premises, FormulaLogicOperator.Implies, conclusion)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
