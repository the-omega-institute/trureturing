using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;
internal sealed class DenseClauseExecutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual dictionary construction and lookup produce a clean dense word.", H("Restored Dense Word Execution"),
        Blocks(Describe.Lean(DescribeId.Create("dense-execution"),
            DeclarationHandle.Create("D5/S0/Computability/DenseClauseExecution.denseExecution"),
            H("Restored Dense Word Execution"), StatementSource.FromAuthor(Presentation()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The actual parser phase is followed by rightmost dictionary deduplication, dimension writing, restored first-index lookups, literal copying, dictionary draining and output reversal. Every raw word reaches the exact clean haltList containing denseConverted within the phase-by-phase denseRunClock. Malformed input takes the actual drain and zero-variable empty-clause source branch. Accepted input has its full original spelling and clause width; the semantic refinement then supplies the quadratic clock and count transport."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/DenseClauseMachine"))]));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Width(Formula clauses) => All("c", Id("Clause"),
        Imp(new Formula.Relation(Id("c"), FormulaRelationOperator.MemberOf, clauses), Le(Call("length", Id("c")), Num(3))));
    private static Formula CleanRun(string machine, Formula w, Formula output, Formula clock) =>
        Call("Nonempty", Call("EvalsToInTime", Call("step", Id(machine)),
            Call("initList", Id(machine), w), Call("some", Call("haltList", Id(machine), output)), clock));
    private static Formula Presentation()
    {
        var w = Id("w");
        var run = CleanRun("denseMachine", w, Call("denseConverted", w), Call("denseRunClock", w));
        var shape = All("F", Id("ConventionalFormula"),
            Imp(Equal(Call("readWord", w), Call("some", Id("F"))),
                And(Equal(w, Call("formulaWord", Id("F"))), Width(Id("F")))));
        return All("w", Call("List", Id("Bool")), And(run, shape));
    }
}
