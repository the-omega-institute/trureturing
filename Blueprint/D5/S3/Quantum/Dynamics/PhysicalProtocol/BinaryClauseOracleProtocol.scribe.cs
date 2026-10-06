using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics.PhysicalProtocol;
internal sealed class BinaryClauseOracleProtocolDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every raw appearing-name clause word executes one physical query and paid response recovery.",
        H("Conventional One Query Physical Protocol"),
        Blocks(Describe.Lean(DescribeId.Create("conventional-one-query-run"),
            DeclarationHandle.Create("D5/S3/Quantum/Dynamics/PhysicalProtocol/BinaryClauseOracleProtocol.conventional_one_query_run"),
            H("Actual compiler, response writes and independent count"),
            StatementSource.FromAuthor(Presentation()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The prefix executes the fixed twenty-three-stack query compiler on the actual raw conventional word. Its exact clean output is the query for the densely prepared raw clauses. The physical phase uses the positive rational whose complex value equals the full matrix exponential trace of that same Hamiltonian at inverse temperature log two, in canonical reduced bare numerator slash denominator spelling. The oracle relation contains no satisfying count or arithmetic suitability premise.")),
                Paragraph(Text("A counted suffix is extracted from the actual unary physical trace, and the compiler trace is lifted instruction by instruction. The entry transition, one distinguished Ask, symbol reads, ordinary response writes, reversal and postprocessor execution are all charged. For input length L and B equal to L squared plus eight L plus seven, the complete time is at most eighty times (L plus one) squared plus twenty B squared plus seventy-two B plus eighty-seven. The response has at most two times (B plus one) squared plus B plus five symbols.")),
                Paragraph(Text("The ordinary post output represents the independent appearing-name satisfying count. Every complete trace has exactly one Ask, including malformed source words routed through the valid zero-variable empty-clause query. All ordinary post scratch is empty and control is reset at halt. The query retains the raw physical clauses; reverse conversion tautologies are not inserted into this Hamiltonian."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/DenseQueryCompiler")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Quantum/Dynamics/PhysicalProtocol/ClauseOracleProtocol"))]));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Presentation()
    {
        var w = Id("w");
        var r = Id("r");
        var length = Call("length", w);
        var b = Add(Add(new Formula.Power(length, Num(2)), Multiply(Num(8), length)), Num(7));
        var query = Call("preparedQuery", Call("denseOutput", w));
        var start = Call("prefix", Call("initList", Id("queryCompiler"), w));
        var finish = Call("physical", Call("halt", Call("haltList", Id("postMachine"), Call("binaryWord", Call("totalPostOutput", r)))));
        var clock = Add(Add(Add(Multiply(Num(80), new Formula.Power(Add(length, Num(1)), Num(2))),
            Multiply(Num(20), new Formula.Power(b, Num(2)))), Multiply(Num(72), b)), Num(87));
        var reply = Call("queryReply", query, r);
        var growth = Le(Call("length", r), Add(Add(Multiply(Num(2), new Formula.Power(Add(b, Num(1)), Num(2))), b), Num(5)));
        var count = Equal(Call("msbValue", Call("totalPostOutput", r)), Call("rawCount", w));
        var execution = Exists("t", Id("Nat"), And(Le(Id("t"), clock),
            Call("BinaryProtocolRun", start, finish, Id("t"), Num(1))));
        var allRuns = All("output", Call("Cfg", Id("postMachine")), All("t", Id("Nat"), All("asks", Id("Nat"),
            new Formula.Logic(Call("BinaryProtocolRun", start, Call("physical", Call("halt", Id("output"))), Id("t"), Id("asks")),
                FormulaLogicOperator.Implies, Equal(Id("asks"), Num(1))))));
        return All("w", Call("List", Id("Bool")), Exists("r", Call("List", Id("ResponseSymbol")),
            And(reply, And(growth, And(count, And(execution, allRuns))))));
    }
}
