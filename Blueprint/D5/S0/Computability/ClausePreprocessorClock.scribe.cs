using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class ClausePreprocessorClockDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every raw Boolean word has a polynomial actual run to a clean terminal configuration.",
        H("Total Clause Machine Clock"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pre-total-clock"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/ClausePreprocessorClock.pre_total_clock"),
                H("All raw words, exact clean halt and written-output growth"),
                StatementSource.FromAuthor(Presentation()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every Boolean input word of length L, the fixed five-stack "
                        + "machine reaches an exact clean haltList configuration in at "
                        + "most (4L plus 20)L plus 13 actual transitions. All input and "
                        + "work stacks are empty and the finite control is reset.")),
                    Paragraph(Text(
                        "The decreasing clock assigns input symbols credit 4L plus 20, "
                        + "backup symbols credit three and query symbols credit one. "
                        + "Header symbols have credit five during coefficient copying "
                        + "and credit one during restoration. Phase constants pay for "
                        + "transitions without an input pop. The remaining input, header "
                        + "and scratch lengths always sum to at most L.")),
                    Paragraph(Text(
                        "Each executed step decreases this clock, including malformed "
                        + "cleanup, coefficient copying, index restoration and output "
                        + "reversal. Strong induction constructs the run. The output "
                        + "length is bounded by the transition bound times the fixed "
                        + "program push bound. This proves termination and writing cost; "
                        + "the identity of the output is a separate word refinement."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Computability/ClauseQueryPreprocessor"))]));

    private static Formula Presentation()
    {
        var w = Id("w");
        var output = Id("out");
        var length = Call("length", w);
        var bound = Add(Multiply(Add(Multiply(Num(4), length), Num(20)), length), Num(13));
        var run = Call("Nonempty", Call("TM2OutputsInTime", Id("preMachine"), w,
            Call("some", output), bound));
        var growth = new Formula.Relation(Call("length", output),
            FormulaRelationOperator.LessThanOrEqual,
            Multiply(bound, Call("programPushBound", Call("m", Id("preMachine")))));
        var body = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("out"),
            Call("List", Id("Bool")), new Formula.Logic(run, FormulaLogicOperator.And, growth));
        return new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("w"),
            Call("List", Id("Bool")), body);
    }
}
