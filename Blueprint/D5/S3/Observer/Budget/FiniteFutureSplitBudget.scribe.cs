using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class FiniteFutureSplitBudgetDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Budget/FiniteFutureSplitBudget.finite_future_split_budget";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite future refinements obey pair and class-count split budgets.",
        H("Finite Future Split Budget"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-future-split-budget"),
            DeclarationHandle.Create(Declaration),
            H("Finite refinements consume a bounded split budget"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The readouts form a finite chain on the same state carrier. Each strict "
                        + "step preserves existing distinctions and splits at least one old "
                        + "observation class.")),
                Paragraph(Text(
                    "The frozen strict-refinement theorem gives the sharp class-count deficit. "
                        + "A nonempty initial image removes one state from that deficit, and the "
                        + "binomial recurrence bounds the remainder by the number of unordered "
                        + "distinct state pairs; the empty carrier is handled separately."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/ConceptDynamics/Refinement/StrictRefinementBound"))]));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Card(Formula value) =>
        Seq(Lvert, Sp, value, Rvert);

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula state = F.Id("X");
        Formula output = F.Id("B");
        Formula steps = F.Id("s");
        Formula readout = F.Id("C");
        Formula index = F.Id("i");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula concept = Call("Concept", state, output);
        Formula readoutAt(Formula at) => Call("C", at);
        Formula initialClasses = Card(Call("range", readoutAt(D(0))));
        Formula stateCount = Card(state);
        Formula strictChain = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(
                FormulaIdentifier.Create("i"), Call("Fin", steps))],
            Call(
                "StrictlyRefines",
                readoutAt(Call("castSucc", index)),
                readoutAt(Call("succ", index))));
        Formula pairBudget = new Formula.Relation(
            steps,
            FormulaRelationOperator.LessThanOrEqual,
            Call("choose", stateCount, D(2)));
        Formula classBudget = new Formula.Relation(
            steps,
            FormulaRelationOperator.LessThanOrEqual,
            Seq(stateCount, Sp, Minus, Sp, initialClasses));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("X"), type),
                new Formula.BoundVariable(FormulaIdentifier.Create("B"), type),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("finiteX"), Call("Finite", state)),
                new Formula.BoundVariable(FormulaIdentifier.Create("s"), naturals),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("C"),
                    Seq(Call("Fin", Seq(steps, Plus, D(1))), Sp, To, Sp, concept)),
                new Formula.BoundVariable(FormulaIdentifier.Create("strict"), strictChain),
            ],
            new Formula.Logic(pairBudget, FormulaLogicOperator.And, classBudget)));
    }
}
