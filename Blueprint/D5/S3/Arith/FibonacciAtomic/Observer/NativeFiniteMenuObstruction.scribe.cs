using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeFiniteMenuObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuObstruction.";

    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] a) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. a]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula NeOf(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula And(params Formula[] a) => Seq(a.Select((f,i) => i == 0 ? Par(f) : Seq(Sp, Land, Sp, Par(f))).ToArray());
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Less(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall, Sp, Seq(ns.Split(',').Select((n,i) => i == 0 ? V(n) : Seq(Comma,Sp,V(n))).ToArray()), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Nil => Call("nil");
    private static Formula Rank(Formula s, Formula u) => Call("code", s, u);
    private static Formula Alpha => Call("of", V("true"));
    private static Formula Beta => Call("of", V("false"));
    private static Formula Len(Formula a) => Call("length", a);
    private static Formula At(Formula a, Formula u, Formula k) => Call("readout", a, Call("iterate", V("substitution"), k, u));
    private static Formula Spine(Formula a, Formula u) => Call("spine", a, u);
    private static Formula Cat(Formula a, Formula b) => Call("append", a, b);


    private static Formula A => Spine(V("a"), Alpha);
    private static Formula B => Spine(V("a"), Beta);
    private static Formula K => Add(Call("pathCost", V("r")), D(1));
    private static Formula Q => Cat(V("a"), V("r"));
    private static Formula Outer(Formula u) => Call("outer", u);
    private static Formula Init(Formula s, Formula u) => Call("initial", s, u);
    private static Formula Fut(Formula s, Formula u) => Call("future", s, u, K);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every missing-prefix actual obstruction", H("Every missing-prefix actual obstruction"), Blocks(
            Paragraph(Text("The original height is the ordered-tree depth with leaves at zero. Family D consists exactly of outer(v)=pair(alpha,v) with height(v)<=D. PublicMenu prefixes each relative literal by R in the original order. The whole-vector identity holds at every natural update count, including blocked suffixes.")),
            Paragraph(Text("For a missing proper prefix a and selected q=ar with r nonempty, use exactly v=spine(a,alpha), vprime=spine(a,beta). The spine is the original FM.21 context. Its height is length(a), and flipping its reached leaf at a produces the other tree. The existing off-leaf flip invariance therefore supplies equality of every selected initial coordinate.")),
            Paragraph(Text("Take one common k=pathCost(r)+1. Atomic navigation reaches beta from alpha and a branch from beta at r. Originally-present transport is applied at a, then the literal append identity transfers those replies to q. It is never applied at initially absent q. The bound length(q)+1<=D makes k<2D and forces D>=2. At D=1 no such missing-prefix case exists.")),
            Describe.Lean(DescribeId.Create("atomic-separator"), DeclarationHandle.Create(Prefix + "atomic_separator"), H("A common atomic separating count at each address"), StatementSource.FromAuthor(Disp(All("r",V("Address"),And(EqOf(At(V("r"),Alpha,K),V("beta")),EqOf(At(V("r"),Beta,K),V("branch")))))), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Here k=pathCost(r)+1. Guarded atomic navigation reaches beta from alpha and the pair (beta,alpha) from beta at that same literal address and count. The unconditional subtree/readout identity transfers these reached roots to the actual four-valued replies."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("every-missing-prefix-obstruction"), DeclarationHandle.Create(Prefix + "every_missing_prefix_obstruction"), H("Whole-vector collision, rank separation and one legal future count"), StatementSource.FromAuthor(Disp(All("D",V("Nat"),All("S",V("Menu"),Imp(All("q",V("Address"),Imp(Mem(V("q"),V("S")),Le(Add(Len(V("q")),D(1)),V("D")))),All("a,r",V("Address"),Imp(And(NeOf(V("r"),Nil),Mem(Q,V("S")),Seq(Neg,Sp,Par(Mem(V("a"),V("S"))))),And(Le(D(2),V("D")),EqOf(Call("height",A),Len(V("a"))),EqOf(Call("height",B),Len(V("a"))),Le(Len(V("a")),Call("sub",V("D"),D(2))),Call("Family",V("D"),Outer(A)),Call("Family",V("D"),Outer(B)),EqOf(Init(V("S"),A),Init(V("S"),B)),EqOf(Init(Call("publicMenu",V("S")),Outer(A)),Init(Call("publicMenu",V("S")),Outer(B))),NeOf(Rank(V("S"),A),Rank(V("S"),B)),Less(K,Mul(D(2),V("D"))),EqOf(At(Call("cons",V("true"),Q),Outer(A),K),V("beta")),EqOf(At(Call("cons",V("true"),Q),Outer(B),K),V("branch")),NeOf(Fut(V("S"),A),Fut(V("S"),B)),NeOf(Fut(Call("publicMenu",V("S")),Outer(A)),Fut(Call("publicMenu",V("S")),Outer(B))))))))))), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("These conclusions all concern the same actual pair and the same supplied count. Each history uses its own fixed original source and genuine repeated substitution. Code inequality uses the original branch-first ranks of this pair, including the eta=0 overlap case. No generic quotient, coordinate-specific source choices or resource-efficiency assertion enters the result."))), DescribeRole.Theorem))));
}
