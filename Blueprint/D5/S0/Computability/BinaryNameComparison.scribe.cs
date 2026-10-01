using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class BinaryNameComparisonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Comparison of whole binary names includes length mismatch and paid restoration.",
        H("Binary Name Comparison"),
        Blocks(Describe.Lean(
            DescribeId.Create("name-compare-run"),
            DeclarationHandle.Create("D5/S0/Computability/BinaryNameComparison.name_compare_run"),
            H("Restored operands, empty backups and preserved caller frame"),
            StatementSource.FromAuthor(Presentation()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For arbitrary Boolean words a and b, previous output and caller frame, "
                + "the six-stack, four-label machine consumes both operands into backups, "
                + "including unequal lengths. It restores each operand, empties both backups, "
                + "pushes their whole-word equality flag onto the previous output and returns "
                + "with its initial control. The caller frame is preserved literally.")),
                Paragraph(Text(
                "The native transition bound is twice the sum of the operand lengths plus "
                + "four. Only symbol comparisons occur; binary names are never expanded "
                + "into unary numbers. This is a routine boundary with restored operands, "
                + "rather than the clean haltList boundary of the complete converter."))),
            DescribeRole.Theorem)), []));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Triple(Formula a, Formula b, Formula c) =>
        F.Seq(F.Open, a, F.Comma, F.Sp, b, F.Comma, F.Sp, c, F.Close);

    private static Formula Presentation()
    {
        var a = Id("a");
        var b = Id("b");
        var output = Id("output");
        var frame = Id("frame");
        var nil = Id("nil");
        var state = Triple(Id("none"), Id("none"), Id("true"));
        var start = Call("compareCfg", Call("some", Id("compare")), state,
            a, b, nil, nil, output, frame);
        var flag = Call("decide", new Formula.Relation(a, FormulaRelationOperator.Equal, b));
        var end = Call("some", Call("compareCfg", Id("none"), state,
            a, b, nil, nil, Call("cons", flag, output), frame));
        var bound = Add(Multiply(Num(2), Add(Call("length", a), Call("length", b))), Num(4));
        var run = Call("Nonempty", Call("EvalsToInTime", Call("step", Id("compareMachine")),
            start, end, bound));
        var word = Call("List", Id("Bool"));
        return All("a", word, All("b", word, All("output", word, All("frame", word, run))));
    }
}
