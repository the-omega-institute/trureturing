using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;
internal sealed class ReverseClauseConversionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed finite word transducer preserves explicitly declared variables through ordinary appearing-name clauses.",
        H("Paid Reverse Clause Word Conversion"),
        Blocks(Describe.Lean(
            DescribeId.Create("reverse-word-run"),
            DeclarationHandle.Create("D5/S0/Computability/ReverseClauseConversion.reverse_word_run"),
            H("Total word execution, canonical names and complete assignment count"),
            StatementSource.FromAuthor(Presentation()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Every raw unary source runs on the fixed ten-stack Boolean program. The actual preprocessor is translated instruction by instruction; subsequent phases scan coefficients, restore counters, write canonical binary names, append tautologies, reverse the output and empty all scratch stacks. The clock is ten times input length squared plus forty-one times input length plus thirty-three.")),
                Paragraph(Text("The conventional output has length at most four times input length squared plus fourteen times input length plus six. Its whole-word decoder returns precisely the renamed clauses and one tautology for each explicitly declared variable. Assignment equivalence preserves the ordinary CNF count, including unused variables. Tautologies occur only in this consumer encoding and leave the original physical clause family unchanged.")),
                Paragraph(Text("The source decoder determines acceptance. Malformed words produce the conventional zero-variable empty-clause word011000 and count zero; valid source0011000 reaches that same output. Empty formulas, empty clauses, zero variables, repeated literals, and opposite polarities remain in scope. Count is defined from ordinary CNF evaluation independently of any physical trace or oracle."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/DenseClauseConversion")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/ReverseClauseMachine"))]));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula CleanRun(string machine, Formula w, Formula output, Formula clock) =>
        Call("Nonempty", Call("EvalsToInTime", Call("step", Id(machine)),
            Call("initList", Id(machine), w), Call("some", Call("haltList", Id(machine), output)), clock));
    private static Formula Presentation()
    {
        var w = Id("w");
        var length = Call("length", w);
        var output = Call("convertedWord", w);
        var run = CleanRun("reverseMachine", w, output,
            Add(Add(Multiply(Num(10), new Formula.Power(length, Num(2))), Multiply(Num(41), length)), Num(33)));
        var growth = Le(Call("length", output), Add(Add(Multiply(Num(4), new Formula.Power(length, Num(2))), Multiply(Num(14), length)), Num(6)));
        var decode = Equal(Call("readWord", output), Call("some", Call("saturatedFormula", Call("snd", Call("preparedFormula", w)))));
        var count = Equal(Call("rawCount", output), Call("explicitRawCount", w));
        return All("w", Call("List", Id("Bool")), And(run, And(growth, And(decode, count))));
    }
}
