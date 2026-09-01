using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Refinement;

internal sealed class HumeInductiveCoreDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Refinement/HumeInductiveCore.hume_inductive_core";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A constant finite past permits incompatible futures, while descent yields prediction.",
        H("Hume Inductive Core"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-past-countermodel-and-descent-prediction"),
            DeclarationHandle.Create(Declaration),
            H("Finite past does not force a law, but descent yields prediction"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The countermodel uses Boolean states. The readout constantPast maps both "
                        + "states to Unit, while identityFuture keeps them distinct. The displayed "
                        + "same-past and different-future witnesses therefore obstruct refinement.")),
                Paragraph(Text(
                    "The positive clause is general. Whenever a prediction is constant on the "
                        + "fibers of a history readout, it refines the canonical factorization "
                        + "through the realized history image.")),
                Paragraph(Text(
                    "Both clauses apply the frozen inductive-sufficiency equivalence directly. "
                        + "No alternative history, prediction, or refinement relation is defined."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula boolean = F.Id("Bool");
        Formula stateType = F.Id("X");
        Formula historyType = F.Id("H");
        Formula predictionType = F.Id("Y");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula past = F.Id("constantPast");
        Formula future = F.Id("identityFuture");
        Formula history = F.Id("h");
        Formula predict = F.Id("K");

        Formula samePast = new Formula.Relation(
            Apply(past, left), FormulaRelationOperator.Equal, Apply(past, right));
        Formula differentFuture = new Formula.Relation(
            Apply(future, left), FormulaRelationOperator.NotEqual, Apply(future, right));
        Formula witness = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("x", boolean), Bound("y", boolean)],
            new Formula.Logic(samePast, FormulaLogicOperator.And, differentFuture));
        Formula countermodel = new Formula.Logic(
            witness,
            FormulaLogicOperator.And,
            new Formula.Not(Call("Refines", future, Call("rangeFactorization", past))));

        Formula positive = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", type),
                Bound("H", type),
                Bound("Y", type),
                Bound("h", Call("Concept", stateType, historyType)),
                Bound("K", Call("Concept", stateType, predictionType)),
            ],
            new Formula.Logic(
                Call("FactorsThrough", predict, history),
                FormulaLogicOperator.Implies,
                Call("Refines", predict, Call("rangeFactorization", history))));

        return F.Disp(new Formula.Logic(
            countermodel, FormulaLogicOperator.And, positive));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
