using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class ClauseMalformedCleanupDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Error cleanup returns the zero-variable, one-empty-clause query descriptor.",
        H("Clause Machine Error Cleanup"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pre-error-cleanup"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/ClauseMalformedCleanup.pre_error_cleanup"),
                H("All stack contents, exact clean halt and linear cleanup time"),
                StatementSource.FromAuthor(Presentation()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "From error entry, every finite control state and all arbitrary "
                        + "Boolean input, header, scratch and partial-query words are "
                        + "included, with the output stack initially empty. The actual fixed machine drains those four stacks, "
                        + "writes the dummy query, resets its control to the initial "
                        + "state and reaches the exact haltList configuration.")),
                    Paragraph(Text(
                        "The transition bound is the sum of the four initial stack "
                        + "lengths plus five. Each pop removes one real symbol. Four "
                        + "empty-stack transitions select the next cleanup phase, and "
                        + "the final fixed statement writes the complete dummy word.")),
                    Paragraph(Text(
                        "The dummy word describes zero hidden variables and one empty "
                        + "raw clause. This result proves cleanup from error "
                        + "entry. The separate parser-to-error-entry run and its complete "
                        + "polynomial bound are required for universal malformed-source "
                        + "correctness."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Computability/ClauseQueryPreprocessor"))]));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Presentation()
    {
        var st = Id("st");
        var i = Id("input");
        var h = Id("header");
        var s = Id("scratch");
        var q = Id("query");
        var start = Call("preCfg", Id("badInput"), st, i, h, s, q, Id("nil"));
        var end = Call("some", Call("haltList", Id("preMachine"), Id("dummyQuery")));
        var bound = Add(Add(Add(Add(Call("length", i), Call("length", h)),
            Call("length", s)), Call("length", q)), Num(5));
        var run = Call("Nonempty", Call("EvalsToInTime", Call("step", Id("preMachine")),
            start, end, bound));
        return All("st", Id("PreControl"), All("input", Call("List", Id("Bool")),
            All("header", Call("List", Id("Bool")), All("scratch", Call("List", Id("Bool")),
                All("query", Call("List", Id("Bool")), run)))));
    }
}
