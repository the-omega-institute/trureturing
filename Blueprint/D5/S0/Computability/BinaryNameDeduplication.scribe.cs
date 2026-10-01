using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class BinaryNameDeduplicationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Occurrence-driven construction writes the rightmost-deduplicated dictionary.",
        H("Binary Name Dictionary Construction"),
        Blocks(Describe.Lean(
            DescribeId.Create("dictionary-build-run"),
            DeclarationHandle.Create("D5/S0/Computability/BinaryNameDeduplication.dictionary_build_run"),
            H("Actual lookup, insertion and a quadratic charged clock"),
            StatementSource.FromAuthor(Presentation()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every list of binary names, the eleven-stack machine scans its "
                + "serialized occurrences in reverse order. It extracts each whole name "
                + "with real pops and invokes the included finite dictionary-lookup program. "
                + "The resulting membership flag selects an actual discard or insertion branch.")),
                Paragraph(Text(
                "Every unseen name is written to the head of the dictionary in escaped "
                + "reversed spelling; the dimension stack receives one true symbol. "
                + "The final dictionary equals the pinned rightmost-occurrence deduplication "
                + "of the original list. All comparison backups, candidates, history, "
                + "index and occurrence stacks are empty at return. The arbitrary caller "
                + "frame and dimension suffix are preserved.")),
                Paragraph(Text(
                "The clock is at most twenty times (serialized occurrence length plus one) "
                + "squared. It charges extraction, comparison, operand and dictionary "
                + "restoration, index draining and insertion. This routine does not yet "
                + "parse arbitrary conventional clause words or relabel their literals."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryNameDictionary"))]));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Triple(Formula a, Formula b, Formula c) =>
        F.Seq(F.Open, a, F.Comma, F.Sp, b, F.Comma, F.Sp, c, F.Close);

    private static Formula Presentation()
    {
        var names = Id("names");
        var frame = Id("frame");
        var dimension = Id("dimension");
        var nil = Id("nil");
        var word = Call("List", Id("Bool"));
        var state = Triple(Triple(Id("none"), Id("none"), Id("true")), Id("none"), Id("false"));
        var start = Call("buildCfg", Id("start"), nil, nil, nil,
            Call("dictionaryStream", Call("reverse", names)), dimension, frame, Id("false"));
        var end = Call("some", Call("builderCfg", Id("none"), state,
            Call("dictionaryStacks", Call("compareStacks", nil, nil, nil, nil, nil, frame),
                Call("dictionaryStream", Call("dedup", names)), nil, nil), nil,
            Call("append", Call("replicate", Call("length", Call("dedup", names)), Id("true")), dimension)));
        var bound = Multiply(Num(20), Call("pow", Add(Call("length", Call("dictionaryStream", names)), Num(1)), Num(2)));
        var run = Call("Nonempty", Call("EvalsToInTime", Call("step", Id("builderMachine")), start, end, bound));
        return All("names", Call("List", word), All("frame", word, All("dimension", word, run)));
    }
}
