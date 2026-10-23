using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController;

internal sealed class RarePriorLiteralControllerLiveProducerExecutionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/LiveProducerExecution.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "RarePriorLiteralController.LiveProducerExecution", H("Captured operations and native key execution"), Blocks(
            Paragraph(Text("A prepared transaction uses the inherited actual Runtime and captured Operation to execute the native dictionary, copy its full return word, address the selected original frame bit, emit that bit and commit the tagged operation. acquisition_commit starts with the actual source-request instruction and retains its own Operation.read value. The passive-port law keeps unrelated source and fresh values out of deterministic steps.")),
            Paragraph(Text("Returns means that a finite run reaches the returned stage. The rank is the least such finite time and is used only in external analysis: it is not a stored clock or instruction input. rank_step strictly decreases before return, and no_fault excludes fault on every cut of a returning execution. These claims are conditional on the returning path; they do not prove totality of every producer state.")),
            Paragraph(Text("For CurrentBank, a carry increment writes exactly the newly reached raw unary query cell. The build-key induction identifies that tape with the encoded native key, while build_exit connects the terminal carry to scanner entry and resident opcode loading. native_bit_correct, opcode_rom, opcode_decode and native_scan_refines connect installed tape reads to the existing nativeTable specification.")),
            Paragraph(Text("The frame law below holds for every state and iteration count, including zero and malformed key rails. It preserves both banks, the captured operation, inherited addressed context, opcode motor and role throughout key building. Only the key and query work can change. This law supplies the physical-bank fetch bridge without replacing a tape read by a decoded Runtime operation.")),
            Describe.Lean(DescribeId.Create("build-key-frame"),
                DeclarationHandle.Create(Prefix + "build_key_frame"), H("Key building preserves the surrounding banks and controls"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each literal carry step preserves the six displayed context components. Induction composes that step relation through every finite iteration; the native fetch uses it together with the independently proved key and query relations."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/LiveProducerSetup"))]));

    private static Formula N(string x) => Seq(Operatorname, Grp(F.Id(x)));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, N(x), Sp, Colon, Sp, type, Close, Comma, Sp, body);
    private static Formula EqF(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Field(Formula a, params string[] names)
    {
        foreach (var name in names) a = Seq(Open, a, Close, Dot, N(name));
        return a;
    }
    private static Formula And(params Formula[] xs)
    {
        var r = xs[^1];
        for (var i = xs.Length - 2; i >= 0; i--)
            r = Seq(Open, Open, xs[i], Close, Sp, Land, Sp, Open, r, Close, Close);
        return r;
    }
    private static Formula Iter(Formula f, Formula n, Formula s) =>
        Seq(Open, f, Close, Caret, Grp(Seq(OpenBracket, n, CloseBracket)), Sp, s);
    private static Formula CState => Seq(N("LiveProducer"), Dot, N("CurrentBank"), Dot, N("State"));
    private static Formula CB(string name) => Seq(N("LiveProducer"), Dot, N("CurrentBank"), Dot, N(name));
    private static Formula Statement()
    {
        var s = N("s"); var q = Iter(CB("buildKey"), N("n"), s);
        var body = And(EqF(Field(q, "actual"), Field(s, "actual")),
            EqF(Field(q, "synthetic"), Field(s, "synthetic")),
            EqF(Field(q, "operation"), Field(s, "operation")),
            EqF(Field(q, "addressed"), Field(s, "addressed")),
            EqF(Field(q, "opcodes"), Field(s, "opcodes")),
            EqF(Field(q, "role"), Field(s, "role")));
        return All("s", CState, All("n", Nat, body));
    }
}
