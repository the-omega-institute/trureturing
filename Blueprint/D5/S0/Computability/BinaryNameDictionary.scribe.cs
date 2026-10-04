using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class BinaryNameDictionaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Whole-name lookup restores the serialized dictionary and reports its dense position.",
        H("Binary Name Dictionary Lookup"),
        Blocks(Describe.Lean(
            DescribeId.Create("dictionary-lookup-run"),
            DeclarationHandle.Create("D5/S0/Computability/BinaryNameDictionary.dictionary_lookup_run"),
            H("Actual finite execution, exact restored words and paid scan clock"),
            StatementSource.FromAuthor(Presentation()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For an arbitrary query name, list of dictionary names and caller frame, "
                + "the nine-stack machine scans the private serialized dictionary. Each "
                + "entry stores its reversed binary spelling in escaped pairs. Real pushes "
                + "extract the candidate, the included comparison program backs up and "
                + "restores both operands, and cleanup drains the candidate stack.")),
                Paragraph(Text(
                "The final index stack contains the membership flag followed by the unary "
                + "first-occurrence index; absence uses the dictionary length sentinel. "
                + "The query and entire dictionary stream are restored literally, all "
                + "backups and comparison output are empty, and the caller frame is "
                + "preserved. The bound is (2 times query length plus 12) times the number "
                + "of names, plus four times serialized dictionary length, plus three.")),
                Paragraph(Text(
                "This is a routine boundary for arbitrary names and dictionary order. "
                + "The theorem does not supply the preceding raw-source parser, rightmost "
                + "deduplication or count-preserving complete converter. Those stages must "
                + "establish the actual dictionary used by this scan."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryNameComparison"))]));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Triple(Formula a, Formula b, Formula c) =>
        F.Seq(F.Open, a, F.Comma, F.Sp, b, F.Comma, F.Sp, c, F.Close);

    private static Formula Presentation()
    {
        var q = Id("query");
        var names = Id("names");
        var frame = Id("frame");
        var nil = Id("nil");
        var word = Call("List", Id("Bool"));
        var stream = Call("dictionaryStream", names);
        var state = Triple(
            Triple(Id("none"), Id("none"), Id("true")),
            Id("none"), Id("false"));
        var start = Call("lookupCfg", Id("start"), q, nil, nil, nil, frame,
            stream, nil, nil, Id("false"));
        var flag = Call("decide", new Formula.Relation(q, FormulaRelationOperator.MemberOf, names));
        var index = Call("replicate", Call("idxOf", q, names), Id("true"));
        var end = Call("some", Call("dictionaryCfg", Id("none"), state,
            Call("compareStacks", q, nil, nil, nil, nil, frame),
            stream, nil, Call("cons", flag, index)));
        var bound = Add(Add(Multiply(Add(Multiply(Num(2), Call("length", q)), Num(12)),
            Call("length", names)), Multiply(Num(4), Call("length", stream))), Num(3));
        var run = Call("Nonempty", Call("EvalsToInTime", Call("step", Id("dictionaryMachine")),
            start, end, bound));
        return All("query", word, All("names", Call("List", word), All("frame", word, run)));
    }
}
