using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class RationalMalformedCleanupDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arbitrary response-error stacks reach the exact clean one-zero terminal state.",
        H("Rational Response Error Cleanup"),
        Blocks(Describe.Lean(
            DescribeId.Create("post-error-cleanup"),
            DeclarationHandle.Create("D5/S0/Computability/RationalMalformedCleanup.post_error_cleanup"),
            H("Arbitrary scratch contents and linear physical erasure"),
            StatementSource.FromAuthor(Presentation()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "At badInput, the finite control and the input, quotient and shift "
                + "stacks may contain arbitrary ternary words. The output stack is "
                + "initially empty. Three actual draining passes erase all remaining "
                + "symbols, write one zero, reset the control and halt with all scratch "
                + "empty. The bound is the three initial lengths plus three.")),
                Paragraph(Text(
                "This theorem starts at error entry. The whole-word refinement "
                + "establishes which parser branches reach that entry. No physical "
                + "oracle or SAT count occurs in this cleanup statement."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/RationalPostprocessor"))]));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Presentation()
    {
        var input = Id("input");
        var quotient = Id("quotient");
        var shifts = Id("shifts");
        var run = Call("Nonempty", Call("EvalsToInTime", Call("step", Id("postMachine")),
            Call("postCfg", Id("badInput"), Id("st"), input, quotient, shifts, Id("nil")),
            Call("some", Call("haltList", Id("postMachine"), Call("singleton", Id("zero")))),
            Add(Add(Add(Call("length", input), Call("length", quotient)), Call("length", shifts)), Num(3))));
        var word = Call("List", Id("ResponseSymbol"));
        return All("st", Id("PostControl"), All("input", word,
            All("quotient", word, All("shifts", word, run))));
    }
}
