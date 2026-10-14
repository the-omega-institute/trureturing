using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeClassRootImageDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact image filling and the finite class-root chart on complete native fibers.",
        H("Native Class Root Images"), Blocks(
            Paragraph(Text("Trees are all nonempty finite ordered Boolean trees. Alpha is the true leaf and beta the false leaf. The original substitution rho sends alpha to beta and beta to pair(beta,alpha), and preserves ordered pairing. A literal row C retains the concrete exterior and all occurrences of shared class names. D=Classes(C) is the finite subtype of appearing Nat labels; raw label gaps and unused Nat labels add no classes.")),
            Entry("evaluate_leaf", "Exact Literal Leaf Evaluation", "For every exterior C, arbitrary valuation f and Boolean leaf b, evaluating C yields exactly b if and only if C is a literal b under the roots of f. The full predecessor factorization uses this criterion at visible sibling roots.", DescribeRole.Theorem),
            Entry("root_extend", "Roots of Extended Valuations", "RootExtend(C,v) abbreviates the function n to rootType(extend(C,v,n)). Its equality with typeExtend(C,types(C,v)) holds on all natural labels, including the off-support alpha default. This identity connects literal evaluation to the finite root assignment.", DescribeRole.Theorem),
            Entry("rootType", "Three Reached Root Types", "Root types are some(true)=alpha, some(false)=beta and none=branch. The empty address is always reached, so there is no absent type.", DescribeRole.Definition),
            Entry("Image", "Actual Substitution Image", "Image membership requires an actual finite predecessor under the original substitution rho.", DescribeRole.Definition),
            Entry("lit", "Literal Leaf Predicate", "A visible pair is never a literal leaf. A class name is a literal leaf exactly when its shared root type is that leaf.", DescribeRole.Definition),
            Entry("im", "Finite Recursive Image Predicate", "AlphaType means some(true). The first pair disjunct is exactly E=pair(beta,alpha); the second is a pair of images. This is the complete NBP.10.4 recursion.", DescribeRole.Definition),
            Entry("BranchImages", "Actual Branch Image Obligations", "Only appearing branch-valued classes require actual image membership. An alpha-valued class is allowed in the right child of E.", DescribeRole.Definition),
            Entry("filling_image_iff", "Exact Test for Every Actual Filling", "RootTypeCompose(f) maps n to rootType(f(n)). Structural induction proves the test for every literal row and every actual valuation. In the exceptional pair case both evaluated children are leaves, so their branch obligations are vacuous. For any legal x on D, put f=extend(C,x); the displayed statement becomes exactly NBP.10.6. A feasible branch type at a root hole does not make pair(alpha,alpha) an image: actual branch membership is required.", DescribeRole.Theorem),
            Entry("typeExtend", "Type Assignment on Appearing Labels", "On the appearing support n denotes its subtype element. Off-support defaults never create extra classes.", DescribeRole.Definition),
            Entry("types", "Roots of Class Values", "The map records the root of every actual appearing class value, with the same value at all repeated occurrences.", DescribeRole.Definition),
            Entry("Admissible", "Exact Finite Feasible Chart", "LeafClasses(theta,b) is the subset of D with theta(d)=some(b). The bounds count distinct classes, not occurrences. Admissible is precisely membership in Theta of NBP.10.5.", DescribeRole.Definition),
            Entry("OriginFiber", "Full Actual One-Image Fiber", "This is U in NBP.10.2. In the realization theorem C is an actual complete canonical row. Every concrete exterior constructor, repeated occurrence, distinct-class disequality and absent-cut strict-prefix blocking leaf remains. Empty and root cuts, blocked members, zero classes and all finite source sizes are included, without rank or history bounds.", DescribeRole.Definition),
            Entry("ImageValues", "Legal Image Fillings", "This is X in NBP.10.1: all injective valuations on D whose filled complete exterior is an actual image.", DescribeRole.Definition),
            Entry("imageOriginEquiv", "Exact Image-Valuation and Origin Bijection", "The forward map is x to delta(evaluateRow(extend(C,x),C)), where delta is the original unique inverse on rho[Source]. The inverse recovers the class subtrees of rho(u) using their canonical representatives. The exact legal-row equivalence and both inverse laws give the NBP.10.3 bijection.", DescribeRole.Definition),
            Entry("class_root_chart", "Exact Types Attained Throughout the Actual Fiber", "Recover(P,rho(u)) abbreviates the legal valuation recovered in the complete row C=canonicalRow(P,t0), with the prefix-free proof supplied. This is exact NBP.10.7 on the entire actual NBP.10.2 domain. Enumerate the finite subtype D through e:D equivalent to Fin(card D). Leaf classes receive their forced leaves. Branch class d receives rho(pair(code(card D,e(d)),alpha)); these are images with branch roots, pairwise distinct by code and substitution injectivity, and distinct from both leaves. The cardinality bounds give full injectivity, and the recursive test gives image membership. The image-origin bijection realizes the assignment. Conversely, any origin recovers an injective image valuation; injectivity allows at most one class at each leaf. The construction includes zero branch classes and zero classes.", DescribeRole.Theorem))));
    private static DocumentBlock Entry(string n, string h, string p, DescribeRole r) => Describe.Lean(
        DescribeId.Create("nativeclassrootimage-"+n.Replace("_","-").ToLowerInvariant()), DeclarationHandle.Create(Prefix+n),
        H(h), StatementSource.FromAuthor(Statement(n)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(p))), r);
    private static Formula Statement(string n) => n switch
    {
        "evaluate_leaf" => All("C",V("LiteralRow"),All("f",Call("Valuation",V("Nat"),V("Source")),All("b",V("Bool"),IffOf(EqOf(Call("evaluateRow",V("f"),V("C")),Call("of",V("b"))),Call("lit",Call("RootTypeCompose",V("f")),V("b"),V("C")))))),
        "root_extend" => All("C",V("LiteralRow"),All("v",Call("Valuation",Call("Classes",V("C")),V("Source")),EqOf(Call("RootExtend",V("C"),V("v")),Call("typeExtend",V("C"),Call("types",V("C"),V("v")))))),
        "rootType" => All("z", V("Source"), EqOf(Call("rootType", V("z")), Call("leafLabel", V("z"), V("empty")))),
        "Image" => All("z", V("Source"), IffOf(Call("Image", V("z")), Some("u", V("Source"), EqOf(Call("rho", V("u")), V("z"))))),
        "lit" => All("theta", Seq(V("Nat"), Sp, To, Sp, Call("Option", V("Bool"))), All("b", V("Bool"), And(All("c", V("Bool"), IffOf(Call("lit", V("theta"), V("b"), Call("leaf", V("c"))), EqOf(V("c"), V("b")))), All("n", V("Nat"), IffOf(Call("lit", V("theta"), V("b"), Call("hole", V("n"))), EqOf(Call("theta", V("n")), Call("some", V("b"))))), All("e", V("LiteralRow"), All("g", V("LiteralRow"), NegOf(Call("lit", V("theta"), V("b"), Call("pair", V("e"), V("g"))))))))),
        "im" => All("theta", Seq(V("Nat"), Sp, To, Sp, Call("Option", V("Bool"))), And(NegOf(Call("im", V("theta"), V("alpha"))), Call("im", V("theta"), V("beta")), All("n", V("Nat"), IffOf(Call("im", V("theta"), Call("hole", V("n"))), NegOf(EqOf(Call("theta", V("n")), V("alphaType"))))), All("e", V("LiteralRow"), All("g", V("LiteralRow"), IffOf(Call("im", V("theta"), Call("pair", V("e"), V("g"))), Or(And(Call("lit", V("theta"), V("false"), V("e")), Call("lit", V("theta"), V("true"), V("g"))), And(Call("im", V("theta"), V("e")), Call("im", V("theta"), V("g"))))))))),
        "BranchImages" => All("C", V("LiteralRow"), All("f", Seq(V("Nat"), Sp, To, Sp, V("Source")), IffOf(Call("BranchImages", V("C"), V("f")), All("n", V("Nat"), Imp(Call("member", V("n"), Call("labels", V("C"))), Imp(EqOf(Call("rootType", Call("f", V("n"))), V("none")), Call("Image", Call("f", V("n"))))))))),
        "filling_image_iff" => All("C", V("LiteralRow"), All("f", Seq(V("Nat"), Sp, To, Sp, V("Source")), IffOf(Call("Image", Call("evaluateRow", V("f"), V("C"))), And(Call("BranchImages", V("C"), V("f")), Call("im", Call("rootTypeCompose", V("f")), V("C")))))),
        "typeExtend" => All("C", V("LiteralRow"), All("theta", Seq(Call("Classes", V("C")), Sp, To, Sp, Call("Option", V("Bool"))), All("n", V("Nat"), And(Imp(Call("member", V("n"), Call("labels", V("C"))), EqOf(Call("typeExtend", V("C"), V("theta"), V("n")), Call("theta", V("n")))), Imp(NegOf(Call("member", V("n"), Call("labels", V("C")))), EqOf(Call("typeExtend", V("C"), V("theta"), V("n")), V("alphaType"))))))),
        "types" => All("C", V("LiteralRow"), All("x", Seq(Call("Classes", V("C")), Sp, To, Sp, V("Source")), All("d", Call("Classes", V("C")), EqOf(Call("types", V("C"), V("x"), V("d")), Call("rootType", Call("x", V("d"))))))),
        "Admissible" => All("C", V("LiteralRow"), All("theta", Seq(Call("Classes", V("C")), Sp, To, Sp, Call("Option", V("Bool"))), IffOf(Call("Admissible", V("C"), V("theta")), And(Call("im", Call("typeExtend", V("C"), V("theta")), V("C")), LeOf(Call("card", Call("leafClasses", V("theta"), V("true"))), F.D(1)), LeOf(Call("card", Call("leafClasses", V("theta"), V("false"))), F.D(1)))))),
        "OriginFiber" => All("P", V("CutSet"), All("C", V("LiteralRow"), EqOf(Call("OriginFiber", V("P"), V("C")), SetOf("u", V("Source"), EqOf(Call("canonicalRow", V("P"), Call("rho", V("u"))), V("C")))))),
        "ImageValues" => All("C", V("LiteralRow"), EqOf(Call("ImageValues", V("C")), SetOf("x", Call("LegalValues", V("C")), Call("Image", Call("evaluateRow", Call("extend", V("C"), V("x")), V("C")))))),
        "imageOriginEquiv" => All("P", V("CutSet"), Imp(Call("CutPrefixFree", V("P")), All("t0", V("Source"), Call("Equiv", Call("ImageValues", Call("canonicalRow", V("P"), V("t0"))), Call("OriginFiber", V("P"), Call("canonicalRow", V("P"), V("t0"))))))),
        "class_root_chart" => All("P", V("CutSet"), Imp(Call("CutPrefixFree", V("P")), All("t0", V("Source"), All("theta", Seq(Call("Classes", Call("canonicalRow", V("P"), V("t0"))), Sp, To, Sp, Call("Option", V("Bool"))), IffOf(Call("Admissible", Call("canonicalRow", V("P"), V("t0")), V("theta")), Some("u", Call("OriginFiber", V("P"), Call("canonicalRow", V("P"), V("t0"))), EqOf(Call("types", Call("canonicalRow", V("P"), V("t0")), Call("recover", V("P"), Call("rho", V("u")))), V("theta")))))))),
        _ => throw new System.ArgumentOutOfRangeException(nameof(n))
    };
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open,f,Close);
    private static Formula Call(string n, params Formula[] a) => new Formula.Apply(Seq(Operatorname,Grp(V(n))),[.. a]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula LeOf(Formula a, Formula b) => Seq(a,Sp,Leq,Sp,b);
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a),Sp,Iff,Sp,Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a),Sp,Implies,Sp,Par(b));
    private static Formula NegOf(Formula a) => Seq(Neg,Sp,Par(a));
    private static Formula And(params Formula[] a) => Seq(a.Select((x,i)=>i==0?Par(x):Seq(Sp,Land,Sp,Par(x))).ToArray());
    private static Formula Or(Formula a,Formula b) => Seq(Par(a),Sp,Lor,Sp,Par(b));
    private static Formula All(string n,Formula t,Formula b) => Seq(Forall,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Some(string n,Formula t,Formula b) => Seq(Exists,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula SetOf(string n,Formula t,Formula b) => Seq(OpenBrace,V(n),Colon,Sp,t,Sp,Vert,Sp,b,CloseBrace);
}
