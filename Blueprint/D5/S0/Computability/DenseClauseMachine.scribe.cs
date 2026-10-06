using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;
internal sealed class DenseClauseMachineDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The translated finite parser restores raw words and identifies complete accepted syntax.", H("Dense Parser Instruction Refinement"),
        Blocks(Describe.Lean(DescribeId.Create("dense-parser-run"),
            DeclarationHandle.Create("D5/S0/Computability/DenseClauseMachine.dense_parser_run"),
            H("Dense Parser Instruction Refinement"), StatementSource.FromAuthor(Presentation()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every raw Boolean word, instruction translation executes the actual parser to the parseReturn boundary within four times input length plus five steps. The input is restored, saved stacks are empty, and the decoder determines the occurrence stream and result flag. A grammar induction on that same word shows that every accepted formula reproduces the complete original spelling and has clauses of width at most three. The endpoint is a parser phase boundary, before dictionary construction and dense output."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryNameDeduplication")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/ClauseWordCodec"))]));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Width(Formula clauses) => All("c", Id("Clause"),
        Imp(new Formula.Relation(Id("c"), FormulaRelationOperator.MemberOf, clauses), Le(Call("length", Id("c")), Num(3))));
    private static Formula Presentation()
    {
        var w = Id("w");
        var stacks = Call("denseParserStacks", Call("parseStacks", w, Id("nil"),
            Call("decodedOccurrences", w), Call("singleton", Call("isSome", Call("readWord", w))), Id("nil")));
        var endpoint = Call("some", Call("Cfg", Call("some", Id("parseReturn")), Id("denseLocal"), stacks));
        var run = Call("Nonempty", Call("EvalsToInTime", Call("step", Id("denseMachine")),
            Call("initList", Id("denseMachine"), w), endpoint, Add(Multiply(Num(4), Call("length", w)), Num(5))));
        var shape = All("F", Id("ConventionalFormula"),
            Imp(Equal(Call("readWord", w), Call("some", Id("F"))),
                And(Equal(w, Call("formulaWord", Id("F"))), Width(Id("F")))));
        return All("w", Call("List", Id("Bool")), And(run, shape));
    }
}
