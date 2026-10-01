using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;
internal sealed class ReverseClauseMachineDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual scans write canonical variable names and consumer tautologies.", H("Explicit Universe Word Execution"),
        Blocks(Describe.Lean(DescribeId.Create("reverse-execution"),
            DeclarationHandle.Create("D5/S0/Computability/ReverseClauseMachine.reverseExecution"),
            H("Explicit Universe Word Execution"), StatementSource.FromAuthor(Presentation()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Every raw unary source runs the fixed reverse program to a clean haltList containing convertedWord within reverseClock. The preprocessor is translated instruction by instruction. Subsequent phases scan the query coefficients, restore index counters, write canonical binary names, append one consumer tautology for each declared variable, clear scratch stacks and reverse output. Tautologies preserve unused assignments in the conventional encoding and do not modify the physical raw clauses."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/ClausePreprocessorRefinement")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/ConventionalClauseWords"))]));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula CleanRun(string machine, Formula w, Formula output, Formula clock) =>
        Call("Nonempty", Call("EvalsToInTime", Call("step", Id(machine)),
            Call("initList", Id(machine), w), Call("some", Call("haltList", Id(machine), output)), clock));
    private static Formula Presentation()
    {
        var w = Id("w");
        return All("w", Call("List", Id("Bool")),
            CleanRun("reverseMachine", w, Call("convertedWord", w), Call("reverseClock", w)));
    }
}
