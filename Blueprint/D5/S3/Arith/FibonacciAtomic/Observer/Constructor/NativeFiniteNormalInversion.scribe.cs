using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;

internal sealed class NativeFiniteNormalInversionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFiniteNormalInversion.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite normal native inverses and symbolic values on an original Presburger partition.",
        H("Finite original values of a passing mode"), Blocks(
            Paragraph(Text("Code is the finite free ordered binary tree with natural ranks at its leaves. expand replaces rank n by the native atom T(n) and preserves pairs. A normal code has no pair of primitive children with ranks n+1 and n, at any node. smart collapses exactly this pattern to rank n+2. encode recursively applies smart to the arbitrary finite Source input, including all mixed and repeated subtrees. It computes a normal code whose expansion is the original source.")),
            Describe.Lean(DescribeId.Create("finite-normal-native-inverse"), DeclarationHandle.Create(Prefix + "finite_normal_inverse"),
                H("Unique finite normal inversion on the actual image"), StatementSource.FromAuthor(Disp(FiniteInverse())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("inverseCode visits every finite code leaf and applies rankInverse, propagating failure and preserving every pair. A successful result D is characterized exactly by shiftCode(t,D)=C, where shiftCode adds t to every leaf. Adding a common t preserves and reflects normality and its exceptional sibling relation. Expansion intertwines that rank shift with the actual native substitution.")),
                    Paragraph(Text("For a normal primitive image, the existing actual atomic predecessor theorem supplies its natural inverse rank. For a normal pair image, the existing exact image grammar applies. A terminal alternative would force the normal pair to be primitive, a contradiction; the recursive alternative gives both child images. Induction constructs the successful inverse. Its expansion is the unique finite original. No inverse is applied outside an actual image."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exact-natural-inverse-rank"), DeclarationHandle.Create(Prefix + "exact_natural_rank_inverse"),
                H("Exact natural inverse indices, including every boundary"), StatementSource.FromAuthor(Disp(RankInverse())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("rankInverse(0,n) returns n. At a positive requested shift it rejects rank zero and cancels one successor from both inputs otherwise. Induction proves success with q exactly when q+t=n. A successful q exists exactly when t is at most n, and the natural equation has at most one q. This covers n=0, t=0, n=t and n<t without natural truncated subtraction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("symbolic-presburger-normal-inverse"), DeclarationHandle.Create(Prefix + "symbolic_presburger_inverse"),
                H("A finite disjoint Presburger partition computes symbolic normal inverses"),
                StatementSource.FromAuthor(Disp(PartitionInverse())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Template is a finite binary code with integer affine expressions at its primitive leaves. templateCode evaluates them at the same integer list xs and converts each to its natural rank. Nonnegative explicitly requires every input index to be nonnegative. normalPartition is a finite binary decision tree: normalize both children, then when both are primitive split on their rank equality a=b+1. The true branch collapses to b+2 and the false branch retains the pair. All other pairs remain. Each path guard is a conjunction of these Presburger equalities or their negations.")),
                    Paragraph(Text("Partition.Leaf is a finite type of branch histories. It preserves distinct paths even when their outputs coincide. Exactly one path guard is true at each xs. Induction proves that its output is nonnegative, normal, and expands to the input value. Actual-image membership then supplies the successful finite inverse. inverseTemplate subtracts t in integer affine syntax, and the proof establishes nonnegativity of each resulting natural index. Its evaluated code is exactly the successful inverseCode result. The natural inverse relation is explicitly q+t=n; no natural clipped subtraction defines an inverse."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-symbolic-finite-shared-value"), DeclarationHandle.Create(Prefix + "original_symbolic_finite_value"),
                H("The symbolic original finite value is shared in every admissible solution"),
                StatementSource.FromAuthor(Disp(OriginalValue())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("I, s and mode are the actual EpochInput, valid potential tuple and computed passing mode from NativeOriginalReconstructionBridge. R contains arbitrary original reconstruction expressions. finiteImageExpressions is the executable symbolic finite pass on the actual normalized common-shift images. Its successful result f is independent of the original parameter tuple. finiteTemplate replaces each finite symbolic residual index by its owning original affine expression plus the fixed offset, retaining arbitrary grounds and mixed pairs. The last token has numerical rank zero and remains the explicit Omega slot in native evaluation; a successful finite symbolic pass never changes Omega into a new free rank.")),
                    Paragraph(Text("For every original p at which originalImageGuard passes, the original guard and all affine nonnegativity conditions hold. finiteTemplate at that same p expands to finiteValue(f). The proved canonical reconstruction identity makes this finite image the actual rho to power commonShift(s) of the original coordinate. The displayed finite partition depends only on the stored finite syntax. At its unique active leaf, the guarded inverse template is a normal finite value equal to the canonical original reconstruction and to that reconstruction in every original admissible solution of the same projected normalized mode, at this same original p.")),
                    Paragraph(Text("Together with original_classification_rigidity_prefix this supplies the canonical finite/infinite classification, symbolic finite rigidity, and terminating prefixes of Theorem 4.4 for the original reconstruction syntax. The finite Presburger partition handles symbolic inversion rather than enumerating p. Non-rational guarded completed values remain in scope for the infinite prefix clause. No assertion requires a canonically infinite value to stay infinite in another solution, and no physical inverse port, query cost or uniform runtime theorem is asserted."))), DescribeRole.Theorem)
        )));

    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname,Grp(V(s))),[..xs]);
    private static Formula Par(Formula x) => Seq(Open,x,Close);
    private static Formula All(string s, Formula t, Formula b) => Seq(Forall,Sp,V(s),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Some(string s, Formula t, Formula b) => Seq(Exists,Sp,V(s),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula EqOf(Formula a, Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a),Sp,Land,Sp,Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a),Sp,Implies,Sp,Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a),Sp,Iff,Sp,Par(b));
    private static Formula Arr(Formula a, Formula b) => Seq(a,Sp,To,Sp,b);
    private static Formula Add(Formula a, Formula b) => Seq(a,Plus,b);
    private static Formula Nat => V("Nat");
    private static Formula True => V("true");
    private static Formula Expand(Formula c) => C("expand",c);
    private static Formula Normal(Formula c) => C("Normal",c);
    private static Formula RankLaw(Formula t, Formula n, Formula q) =>
        IffOf(EqOf(C("rankInverse",t,n),C("some",q)),EqOf(Add(q,t),n));
    private static Formula FiniteInverse()
    {
        Formula Property(Formula d) => And(EqOf(C("inverseCode",V("t"),C("encode",V("g"))),C("some",d)),
            And(Normal(d),EqOf(C("substitutionPower",V("t"),Expand(d)),V("g"))));
        var unique=Some("D",V("Code"),And(Property(V("D")),All("E",V("Code"),Imp(Property(V("E")),EqOf(V("E"),V("D"))))));
        return All("t",Nat,All("g",V("Source"),Imp(C("NativeImage",V("t"),C("embed",V("g"))),
            And(Normal(C("encode",V("g"))),And(EqOf(Expand(C("encode",V("g"))),V("g")),unique)))));
    }
    private static Formula RankInverse() => All("t",Nat,All("n",Nat,
        And(All("q",Nat,RankLaw(V("t"),V("n"),V("q"))),And(
            IffOf(Some("q",Nat,EqOf(C("rankInverse",V("t"),V("n")),C("some",V("q")))),Seq(V("t"),Le,Sp,V("n"))),
            All("q",Nat,All("r",Nat,Imp(EqOf(Add(V("q"),V("t")),V("n")),
                Imp(EqOf(Add(V("r"),V("t")),V("n")),EqOf(V("q"),V("r"))))))))));
    private static Formula UniqueLeaf(Formula p, Formula xs) => Some("l",C("Leaf",p),And(
        EqOf(C("qfEval",C("guard",p,V("l")),xs),True),All("other",C("Leaf",p),Imp(
            EqOf(C("qfEval",C("guard",p,V("other")),xs),True),EqOf(V("other"),V("l"))))));
    private static Formula PartitionInverse()
    {
        var p=C("normalPartition",V("T")); var xs=V("xs");
        var inverse=C("inverseTemplate",V("t"),C("output",p,V("l")));
        var code=C("templateCode",xs,inverse);
        var body=And(UniqueLeaf(p,xs),All("l",C("Leaf",p),Imp(EqOf(C("qfEval",C("guard",p,V("l")),xs),True),
            And(C("Nonnegative",xs,inverse),And(Normal(code),And(
                EqOf(C("substitutionPower",V("t"),Expand(code)),Expand(C("templateCode",xs,V("T")))),
                All("n",Nat,All("q",Nat,RankLaw(V("t"),V("n"),V("q"))))))))));
        return All("T",V("Template"),All("t",Nat,All("xs",C("List",V("Int")),
            Imp(C("Nonnegative",xs,V("T")),Imp(C("NativeImage",V("t"),C("embed",Expand(C("templateCode",xs,V("T"))))),body)))));
    }
    private static Formula OriginalValue()
    {
        var input=V("I"); var s=V("s"); var mode=V("mode"); var p=V("p");
        var j=C("functionalInput",input,s); var xs=C("environment",p); var t=C("commonShift",s);
        var part=C("normalPartition",C("finiteTemplate",C("base",input),V("f")));
        var inverse=C("inverseTemplate",t,C("output",part,V("l")));
        var code=C("templateCode",xs,inverse); var value=C("embed",Expand(code));
        Formula Eval(Formula v) => C("evaluate",C("ranks",C("base",input),p),v,C("R",V("i")));
        var canonical=C("canonicalOriginal",input,s,V("valid"),mode,p,V("passing"));
        var allSolutions=All("v",Arr(C("Fin",V("m")),V("CompletionTree")),
            Imp(C("OriginalAdmissible",input,p,V("v")),Imp(C("EffectiveInMode",j,mode,p,C("imageValues",s,V("v"))),EqOf(Eval(V("v")),value))));
        var body=And(UniqueLeaf(part,xs),All("l",C("Leaf",part),Imp(EqOf(C("qfEval",C("guard",part,V("l")),xs),True),
            And(C("Nonnegative",xs,inverse),And(Normal(code),And(EqOf(Eval(canonical),value),
                And(allSolutions,All("nrank",Nat,All("q",Nat,RankLaw(t,V("nrank"),V("q")))))))))));
        return All("n",Nat,All("k",Nat,All("m",Nat,All("r",Nat,
            All("I",C("EpochInput",V("n"),V("k"),V("m")),All("s",Arr(C("Fin",V("m")),Nat),
            All("valid",C("Potential",input,s),All("mode",C("EffectiveMode",j),
            All("R",Arr(C("Fin",V("r")),C("Expression",V("k"),V("m"))),All("i",C("Fin",V("r")),
            All("f",C("FiniteExpression",Add(V("k"),F.D(1))),
            Imp(EqOf(C("finiteImageExpressions",input,s,mode,V("R"),V("i")),C("some",V("f"))),
            All("p",Arr(C("Fin",V("n")),Nat),All("passing",C("holds",C("originalImageGuard",j,mode),xs),body)))))))))))))));
    }
}
