using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class ClauseQueryPreprocessorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed finite transducer preserves raw unary clauses in a succinct query word.",
        H("Unary Clause Query Preparation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pre-query-run"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/ClauseQueryPreprocessor.pre_query_run"),
                H("Exact query output and quadratic native runtime"),
                StatementSource.FromAuthor(Presentation()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an explicit universe of n variables and raw clauses with "
                        + "at most three literals each, indices are unary and strictly "
                        + "below n. The source word contains the unary universe, clause "
                        + "tags, literal polarities and terminated indices; it is the "
                        + "input to source validation. The physical query is its output. The fixed "
                        + "program has five Boolean stacks, nineteen labels and "
                        + "thirty-six control states.")),
                    Paragraph(Text(
                        "The exact native run produces the fixed query framing, the "
                        + "universe and one coefficient n plus one for each unchanged raw "
                        + "clause. It clears every input and work stack, resets the finite "
                        + "state, and halts with only the output word. If L is the complete "
                        + "source length, its transitions are bounded by three times "
                        + "(L plus three) squared, plus seven.")),
                    Paragraph(Text(
                        "The exact output length is L plus six plus the number of "
                        + "clauses times (n plus two). Empty formulas, empty clauses, "
                        + "repeated literals, tautologies and unused variables are "
                        + "all included without changing the physical clauses."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The concrete source 0011000 encodes zero variables and one empty "
                + "clause. It is accepted and produces the same physical dummy query "
                + "used by rejection cleanup. The source decoder and execution phase "
                + "determine acceptance; equality of physical outputs does not.")),
            Paragraph(Text(
                "The proved run is for valid encoded formulas. Total word decoding, "
                + "malformed-word correctness and the conventional appearing-variable "
                + "counting correspondence are separate obligations."))),
        []));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Presentation()
    {
        var n = Id("n");
        var f = Id("F");
        var source = Call("sourceWord", f);
        var query = Call("queryWord", f);
        var length = Call("length", source);
        var width = All("c", f, new Formula.Relation(Call("length", Id("c")),
            FormulaRelationOperator.LessThanOrEqual, Num(3)));
        var bound = Add(Multiply(Num(3), new Formula.Power(Add(length, Num(3)), Num(2))), Num(7));
        var run = Call("Nonempty", Call("TM2OutputsInTime", Id("preMachine"), source,
            Call("some", query), bound));
        var output = Equal(Call("length", query),
            Add(Add(length, Num(6)), Multiply(Call("length", f), Add(n, Num(2)))));
        return All("n", Id("Nat"), All("F", Call("UnaryFormula", n),
            new Formula.Logic(width, FormulaLogicOperator.Implies,
                new Formula.Logic(run, FormulaLogicOperator.And, output))));
    }
}
