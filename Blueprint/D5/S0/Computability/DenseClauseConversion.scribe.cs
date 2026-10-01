using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class DenseClauseConversionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed finite word machine densely names every appearing variable and preserves the ordinary clause count.",
        H("Paid Dense Clause Word Conversion"),
        Blocks(Describe.Lean(
            DescribeId.Create("dense-word-run"),
            DeclarationHandle.Create("D5/S0/Computability/DenseClauseConversion.dense_word_run"),
            H("Total raw words, clean finite execution and assignment transport"),
            StatementSource.FromAuthor(Presentation()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The source problem counts assignments to exactly the distinct canonical "
                    + "binary names appearing in the decoded ordinary clauses. A malformed "
                    + "word has count zero. The dictionary retains the rightmost occurrence "
                    + "of each name, and its first-index lookup determines the dense unary variable.")),
                Paragraph(Text(
                    "One fixed eighteen-stack Boolean machine runs the whole-word parser, "
                    + "constructs the dictionary with paid comparisons and restoration, writes "
                    + "the explicit dimension and every dense literal index, clears the dictionary "
                    + "and reverses the output. All scratch stacks and finite control reset in "
                    + "the exact haltList configuration. Its direct bound is eighty times (input "
                    + "length plus one) squared. The returned word has length at most "
                    + "the square of input length plus eight times input length plus seven.")),
                Paragraph(Text(
                    "The returned source decodes to the total prepared explicit-universe "
                    + "formula and every clause has at most three literals. An assignment "
                    + "equivalence through the actual deduplicated dictionary preserves ordinary "
                    + "CNF evaluation and the number of satisfying assignments. Rejection returns "
                    + "the valid zero-variable one-empty-clause source 0011000. That same word "
                    + "can also arise from a valid empty-clause source; output equality does not "
                    + "characterize rejection. Empty formulas, repeated literals and tautologies "
                    + "are included. No Hamiltonian or oracle occurs in this counting definition."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/DenseClauseExecution")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/ClauseWordCodec"))]));

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
        var length = Call("length", w);
        var output = Call("denseOutput", w);
        var prepared = Call("densePrepared", w);
        var clauses = Call("snd", prepared);
        var run = CleanRun("denseMachine", w, output,
            Multiply(Num(80), new Formula.Power(Add(length, Num(1)), Num(2))));
        var growth = Le(Call("length", output), Add(Add(new Formula.Power(length, Num(2)), Multiply(Num(8), length)), Num(7)));
        var decode = Equal(Call("readWord", Id("false"), output), Call("some", prepared));
        var count = Equal(Call("unaryCount", clauses), Call("rawCount", w));
        return All("w", Call("List", Id("Bool")), And(run, And(growth, And(decode, And(Width(clauses), count)))));
    }
}
