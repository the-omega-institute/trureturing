using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeSerialImageDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialImage.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeSerialImage", H("NativeSerialImage"), Blocks(
            Entry("terminal_prefix_free", "Prefix-free terminal reply words", "A terminal reply word cannot be a proper prefix of another terminal word for the same source-free control and initial epoch. A prefix relation forces equality of the entire physical action traces and complete outputs, including every silent step and update.", DescribeRole.Theorem),
            Entry("pad", "Fixed-length reply padding", "Pad a bounded terminal reply word with absent symbols to length K. This is a proof construction on words, not a physical register operation. Prefix-freeness makes the padding injective on actual terminal words.", DescribeRole.Definition),
            Entry("bounded_serial_output_image", "Sharp whole-output image bound", "The terminal words inject into the length-K four-valued words. The entire terminal output image therefore lies in a finite set of cardinality at most four to the power K. K equal to zero is included; repeated reads are counted separately. No finite source or output universe and no uniform runtime hypothesis is used.", DescribeRole.Theorem)
        )));
    private static DocumentBlock Entry(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("nativeserialimage-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            role == DescribeRole.Theorem ? StatementSource.FromAuthor(Disp(Statement(name))) : StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Statement(string name) => name switch
    {
        "terminal_prefix_free" => Program(All("N",V("Nat"),All("u,v",V("Source"),All("t,s",V("Trace"),All("o,p",V("O"),Imp(Call("Run",V("delta"),V("c"),V("N"),V("u"),V("t"),V("o")),Imp(Call("Run",V("delta"),V("c"),V("N"),V("v"),V("s"),V("p")),Imp(PrefixOf(Ans("t"),Ans("s")),And(EqOf(V("t"),V("s")),EqOf(V("o"),V("p"))))))))))),
        "bounded_serial_output_image" => Program(All("N,K",V("Nat"),All("U",Call("Set",V("Source")),Imp(Call("Nonempty",V("U")),All("F",Arr(V("Source"),V("O")),Imp(Correct(),Some("labels",Call("Finset",V("O")),And(Le(Call("card",V("labels")),Call("power",D(4),V("K"))),All("u",V("Source"),Imp(Mem(V("u"),V("U")),Mem(Call("F",V("u")),V("labels")))))))))))),
        _ => throw new ArgumentException(name)
    };

    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(params Formula[] fs) => Seq(fs.Select((f, i) => i == 0 ? Par(f) : Seq(Sp, Land, Sp, Par(f))).ToArray());
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Some(string ns, Formula t, Formula b) => Seq(Exists, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Ans(string t) => Call("answers", V(t));
    private static Formula Len(Formula t) => Call("length", t);
    private static Formula Root(string e, string u) => Call("iterate", V("substitution"), V(e), V(u));
    private static Formula RunAt(string root, string trace, Formula output) => Call("Run", V("delta"), V("c"), V("N"), Root("N",root), V(trace), output);
    private static Formula Program(Formula body) => All("C,O", V("Type"), All("delta", Arr(V("C"),Call("Op",V("C"),V("O"))), All("c",V("C"),body)));
    private static Formula PrefixOf(Formula a, Formula b) => Call("IsPrefix",a,b);
    private static Formula Correct() => All("u",V("Source"),Imp(Mem(V("u"),V("U")),Some("t",V("Trace"),And(RunAt("u","t",Call("F",V("u"))),Le(Len(Ans("t")),V("K"))))));
}
