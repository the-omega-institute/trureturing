using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeClassRootPaddingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootPadding.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite image padding realizes every feasible class-root assignment with exact bounded native replies.",
        H("Native Class Root Padding"), Blocks(
            Paragraph(Text("Sources are all finite nonempty ordered Boolean trees. The substitution rho sends alpha to beta, sends beta to pair(beta,alpha), and preserves pairing. For a prefix-free finite cut P and a source t0, write C=canonicalRow(P,t0). Its occurring class set D=Classes(C) identifies repeated holes. ImageValues(C) consists of injective class valuations whose complete filling is an actual rho image; OriginFiber(P,C) consists of all finite origins with complete current row C. No source-size bound is imposed.")),
            Entry("rootReply", "Reached Constructor Reply", "The three root types some(true), some(false), and none mean alpha, beta, and branch respectively. An actual class root is reached, so it has no absent type.", DescribeRole.Definition),
            Entry("queryReply", "Exterior and First-Class Query Rule", "Follow the fixed exterior until a concrete reply or a class hole is encountered. Only that one class type is inspected. An empty suffix returns its constructor. A nonempty suffix returns absent for either leaf type and branch for a branch type. Thus concrete blocking leaves, absent addresses, root holes and repeated-class occurrences are included.", DescribeRole.Definition),
            Entry("DeepValues", "Inclusive Branch Depth", "Every address of length at most L inside a branch-valued class returns branch. In particular no such class has a leaf at depth at most L; its minimum native leaf depth is strictly greater than L.", DescribeRole.Definition),
            Entry("padded_native_query_chart", "Simultaneous Actual Padding and Query Correspondence", "For each admissible assignment theta, one finite valuation and one actual origin satisfy all displayed conclusions together. Different classes remain distinct and every repeated occurrence uses its class value. Branch classes receive distinct image codes duplicated into complete binary trees of depth L+1. Duplication preserves injectivity and image membership; induction on addresses proves the branch-depth bound. Leaf classes receive their forced literals, whose multiplicity bounds ensure injectivity across the entire valuation. The exact image grammar and legal-row theorem give the original finite origin. Structural induction through the exterior then gives every bounded native reply on this same image. Choosing these valuations for all admissible theta gives the simultaneous family, including zero classes and zero branch classes. No cross-origin distinction is required. The chosen finite origins are representatives, not a reconstruction of every source. The result supplies no acquisition permission, runtime query extraction, physical operation or controller-state bound.", DescribeRole.Theorem))));
    private static DocumentBlock Entry(string n, string h, string p, DescribeRole r) => Describe.Lean(
        DescribeId.Create("nativeclassrootpadding-"+n.Replace("_","-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix+n), H(h), StatementSource.FromAuthor(Statement(n)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(p))), r);
    private static Formula Statement(string n) => n switch
    {
        "rootReply" => And(
            EqOf(Call("rootReply", Call("some", V("true"))), V("alpha")),
            EqOf(Call("rootReply", Call("some", V("false"))), V("beta")),
            EqOf(Call("rootReply", V("none")), V("branch"))),
        "queryReply" => All("theta", Fn(V("Nat"), Call("Option", V("Bool"))), And(
            All("a", V("Address"), All("b", V("Bool"),
                EqOf(Call("queryReply", V("theta"), V("a"), Call("leaf", V("b"))),
                    Call("readout", V("a"), Call("leaf", V("b")))))),
            All("d", V("Nat"),
                EqOf(Call("queryReply", V("theta"), V("empty"), Call("hole", V("d"))),
                    Call("rootReply", Call("theta", V("d"))))),
            All("d", V("Nat"), All("a", V("Address"), Imp(NegOf(EqOf(V("a"), V("empty"))),
                And(Imp(EqOf(Call("theta", V("d")), V("none")),
                    EqOf(Call("queryReply", V("theta"), V("a"), Call("hole", V("d"))), V("branch"))),
                    Imp(NegOf(EqOf(Call("theta", V("d")), V("none"))),
                    EqOf(Call("queryReply", V("theta"), V("a"), Call("hole", V("d"))), V("absent"))))))),
            All("l", V("LiteralRow"), All("r", V("LiteralRow"), And(
                EqOf(Call("queryReply", V("theta"), V("empty"), Call("pair", V("l"), V("r"))), V("branch")),
                All("a", V("Address"), And(
                    EqOf(Call("queryReply", V("theta"), Call("left", V("a")), Call("pair", V("l"), V("r"))),
                        Call("queryReply", V("theta"), V("a"), V("l"))),
                    EqOf(Call("queryReply", V("theta"), Call("right", V("a")), Call("pair", V("l"), V("r"))),
                        Call("queryReply", V("theta"), V("a"), V("r")))))))))),
        "DeepValues" => All("C", V("LiteralRow"), All("L", V("Nat"), All("v", Fn(Call("Classes", V("C")), V("Source")),
            IffOf(Call("DeepValues", V("C"), V("L"), V("v")),
                All("d", Call("Classes", V("C")), Imp(EqOf(Call("rootType", Call("v", V("d"))), V("none")),
                    All("a", V("Address"), Imp(LeOf(Call("length", V("a")), V("L")),
                        EqOf(Call("readout", V("a"), Call("v", V("d"))), V("branch")))))))))),
        "padded_native_query_chart" => All("P", V("CutSet"), Imp(Call("CutPrefixFree", V("P")),
            All("t0", V("Source"), All("L", V("Nat"), All("theta", Fn(Call("Classes", Call("canonicalRow", V("P"), V("t0"))), Call("Option", V("Bool"))),
                Imp(Call("Admissible", Call("canonicalRow", V("P"), V("t0")), V("theta")),
                    Some("v", Call("ImageValues", Call("canonicalRow", V("P"), V("t0"))), Some("u", Call("OriginFiber", V("P"), Call("canonicalRow", V("P"), V("t0"))),
                        And(EqOf(Call("rho", V("u")), Call("evaluateRow", Call("extend", Call("canonicalRow", V("P"), V("t0")), V("v")), Call("canonicalRow", V("P"), V("t0")))),
                            EqOf(Call("types", Call("canonicalRow", V("P"), V("t0")), V("v")), V("theta")),
                            Call("DeepValues", Call("canonicalRow", V("P"), V("t0")), V("L"), V("v")),
                            All("a", V("Address"), Imp(LeOf(Call("length", V("a")), V("L")),
                                EqOf(Call("readout", V("a"), Call("rho", V("u"))),
                                    Call("queryReply", Call("typeExtend", Call("canonicalRow", V("P"), V("t0")), V("theta")), V("a"), Call("canonicalRow", V("P"), V("t0"))))))))))))))),
        _ => throw new System.ArgumentOutOfRangeException(nameof(n))
    };
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open,f,Close);
    private static Formula Call(string n, params Formula[] a) => new Formula.Apply(Seq(Operatorname,Grp(V(n))),[.. a]);
    private static Formula Fn(Formula a, Formula b) => Seq(a,Sp,To,Sp,b);
    private static Formula EqOf(Formula a, Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula LeOf(Formula a, Formula b) => Seq(a,Sp,Leq,Sp,b);
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a),Sp,Iff,Sp,Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a),Sp,Implies,Sp,Par(b));
    private static Formula NegOf(Formula a) => Seq(Neg,Sp,Par(a));
    private static Formula And(params Formula[] a) => Seq(a.Select((x,i)=>i==0?Par(x):Seq(Sp,Land,Sp,Par(x))).ToArray());
    private static Formula All(string n,Formula t,Formula b) => Seq(Forall,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Some(string n,Formula t,Formula b) => Seq(Exists,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
}
