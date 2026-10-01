using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics.PhysicalProtocol;

internal sealed class ClauseOracleProtocolDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual preprocessing, one physical ask, paid response writes and postprocessing.",
        H("One Query Operational Protocol"),
        Blocks(Describe.Lean(
            DescribeId.Create("one-query-run"),
            DeclarationHandle.Create("D5/S3/Quantum/Dynamics/PhysicalProtocol/ClauseOracleProtocol.one_query_run"),
            H("All-input execution with exactly one ask and a direct quadratic clock"),
            StatementSource.FromAuthor(Presentation()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every raw Boolean source word, the actual pre-machine emits the "
                + "decoded physical query or the valid zero-variable one-empty-clause "
                + "fallback. The ask relates its whole decoded query to a positive "
                + "reduced rational whose complex cast equals the full physical trace. "
                + "That relation contains no satisfying-count premise.")),
                Paragraph(Text(
                "The ask exposes a read-only external stream while ordinary writable "
                + "response stacks are empty. Each symbol is read into finite control "
                + "in one transition, then written by the fixed materialization machine "
                + "in a separate actual transition. A real reversal puts the response "
                + "on the post input stack. The handoff preserves all those stack "
                + "contents and changes only the fixed control and label.")),
                Paragraph(Text(
                "The response length is at most twice (L plus one) squared plus L "
                + "plus five. The complete run uses at most sixteen L squared plus "
                + "fifty L plus seventy-one transitions. Its final configuration is "
                + "the exact clean post halt for the canonical binary count. Every "
                + "complete run has exactly one ask, including malformed sources. "
                + "The count is over the decoded explicit variable universe; "
                + "conventional appearing-name word conversion is separate."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/ClausePreprocessorRefinement")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Quantum/Dynamics/PhysicalProtocol/PhysicalRationalResponse"))]));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Presentation()
    {
        var w = Id("w");
        var r = Id("r");
        var l = Call("length", w);
        var t = Id("t");
        var asks = Id("asks");
        var initial = Call("pre", Call("initList", Id("preMachine"), w));
        var output = Call("totalPostOutput", r);
        var terminal = Call("halt", Call("haltList", Id("postMachine"), Call("binaryWord", output)));
        var run = Exists("t", Id("Nat"), And(
            Le(t, Add(Add(Multiply(Num(16), new Formula.Power(l, Num(2))),
                Multiply(Num(50), l)), Num(71))), Call("ProtocolRun", initial, terminal, t, Num(1))));
        var universal = All("o", Call("Cfg", Id("postMachine")), All("t", Id("Nat"),
            All("asks", Id("Nat"), new Formula.Logic(
                Call("ProtocolRun", initial, Call("halt", Id("o")), t, asks),
                FormulaLogicOperator.Implies, Equal(asks, Num(1))))));
        var length = Le(Call("length", r),
            Add(Add(Multiply(Num(2), new Formula.Power(Add(l, Num(1)), Num(2))), l), Num(5)));
        var count = Equal(Call("msbValue", output),
            Call("satisfyingCount", Call("snd", Call("preparedFormula", w))));
        return All("w", Call("List", Id("Bool")), Exists("r", Call("List", Id("ResponseSymbol")),
            And(Call("queryReply", Call("preparedQuery", w), r),
                And(length, And(count, And(run, universal))))));
    }
}
