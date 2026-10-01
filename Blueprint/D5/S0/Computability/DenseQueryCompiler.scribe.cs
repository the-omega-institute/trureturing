using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;
internal sealed class DenseQueryCompilerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed finite compiler executes dense naming and pays for every transfer into physical query construction.",
        H("Paid Dense Physical Query Compiler"),
        Blocks(Describe.Lean(
            DescribeId.Create("dense-query-run"),
            DeclarationHandle.Create("D5/S0/Computability/DenseQueryCompiler.dense_query_run"),
            H("Actual complete word execution and independent count"),
            StatementSource.FromAuthor(Presentation()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The compiler has twenty-three Boolean stacks and fixed finite labels and control. It translates every instruction of the actual dense converter and unary preprocessor. When the dense program finishes, two ordinary transfer loops move the output into the preprocessor input, charging twice the output length plus two transitions. All intermediate source, dictionary, saved, and query stacks are empty at the exact clean halt.")),
                Paragraph(Text("For raw source length L and B equal to L squared plus eight L plus seven, the direct clock is eighty times (L plus one) squared plus four B squared plus twenty-two B plus fifteen. The returned whole word decodes as a physical query for precisely the densely prepared raw clause family. Its ordinary explicit-universe count equals the conventional appearing-name count, which is defined independently of the Hamiltonian and oracle.")),
                Paragraph(Text("Every malformed word reaches the valid zero-variable one-empty-clause query. The same query can follow a valid empty-clause source, so validation follows the decoder rather than equality with the dummy word. The theorem proves query construction and paid ordinary execution; the physical response and distinguished Ask are supplied by the separate physical protocol."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/DenseClauseConversion")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/ClausePreprocessorRefinement"))]));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula CleanRun(string machine, Formula w, Formula output, Formula clock) =>
        Call("Nonempty", Call("EvalsToInTime", Call("step", Id(machine)),
            Call("initList", Id(machine), w), Call("some", Call("haltList", Id(machine), output)), clock));
    private static Formula Presentation()
    {
        var w = Id("w");
        var length = Call("length", w);
        var b = Add(Add(new Formula.Power(length, Num(2)), Multiply(Num(8), length)), Num(7));
        var output = Call("preparedQuery", Call("denseOutput", w));
        var clock = Add(Add(Add(Multiply(Num(80), new Formula.Power(Add(length, Num(1)), Num(2))),
            Multiply(Num(4), new Formula.Power(b, Num(2)))), Multiply(Num(22), b)), Num(15));
        var run = CleanRun("queryCompiler", w, output, clock);
        var decode = Equal(Call("readWord", Id("true"), output), Call("some", Call("densePrepared", w)));
        var count = Equal(Call("unaryCount", Call("snd", Call("densePrepared", w))), Call("rawCount", w));
        return All("w", Call("List", Id("Bool")), And(run, And(decode, count)));
    }
}
