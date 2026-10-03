using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class ConventionalClauseWordsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conventional clause parsing has an actual finite scan and exact restored source.",
        H("Conventional Appearing Name Clause Words"),
        Blocks(Describe.Lean(
            DescribeId.Create("conventional-word-run"),
            DeclarationHandle.Create("D5/S0/Computability/ConventionalClauseWords.conventional_word_run"),
            H("Whole-word parser execution and paid occurrence materialization"),
            StatementSource.FromAuthor(Presentation()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Names are positive most significant bit first binary spellings, escaped as "
                + "one followed by each bit and terminated by zero. Each clause has at most "
                + "three signed literals. The formula ends in exactly two zeros. There is "
                + "no explicit variable-universe header: assignments in the independent "
                + "raw count range over exactly the distinct names appearing in the decoded clauses.")),
                Paragraph(Text(
                "For every raw Boolean word and caller frame, the five-stack finite parser "
                + "scans the actual input, saves each consumed symbol, writes escaped name "
                + "occurrences, and restores the original word literally. Accepted words "
                + "return the decoder's reversed occurrence stream and the flag true. "
                + "Rejected words return an empty occurrence stack and the flag false. "
                + "Missing or noncanonical names, fourth literals, truncation and trailing "
                + "symbols take the actual cleanup branch. The saved stack is empty, the "
                + "control is reset and the arbitrary caller frame is preserved.")),
                Paragraph(Text(
                "The bound is four times raw input length plus five. The statement is a "
                + "parser routine boundary with restored source and occurrence output; "
                + "dense relabeling, assignment transport and the complete physical protocol "
                + "require the further word conversion stages."))),
            DescribeRole.Theorem)), []));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Presentation()
    {
        var w = Id("w");
        var frame = Id("frame");
        var nil = Id("nil");
        var start = Call("parseCfg", Call("some", Id("scan")), Id("bodyFirst"), Num(0),
            w, nil, nil, nil, frame, Id("false"));
        var end = Call("some", Call("parseCfg", Id("none"), Id("bodyFirst"), Num(0),
            w, nil, Call("decodedOccurrences", w),
            Call("singleton", Call("isSome", Call("readWord", w))), frame, Id("false")));
        var run = Call("Nonempty", Call("EvalsToInTime", Call("step", Id("parseMachine")),
            start, end, Add(Multiply(Num(4), Call("length", w)), Num(5))));
        var word = Call("List", Id("Bool"));
        return All("w", word, All("frame", word, run));
    }
}
