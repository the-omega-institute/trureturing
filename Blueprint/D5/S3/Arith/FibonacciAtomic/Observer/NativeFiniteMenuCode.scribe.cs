using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeFiniteMenuCodeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuCode.";

    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] a) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. a]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula NeOf(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula And(params Formula[] a) => Seq(a.Select((f,i) => i == 0 ? Par(f) : Seq(Sp, Land, Sp, Par(f))).ToArray());
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Less(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall, Sp, Seq(ns.Split(',').Select((n,i) => i == 0 ? V(n) : Seq(Comma,Sp,V(n))).ToArray()), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Nil => Call("nil");
    private static Formula Left(Formula s) => Call("child", V("false"), s);
    private static Formula Right(Formula s) => Call("child", V("true"), s);
    private static Formula Number(Formula s) => Call("N", s);
    private static Formula Rank(Formula s, Formula u) => Call("code", s, u);
    private static Formula J(Formula s) => Mul(Number(Left(s)), Number(Right(s)));
    private static Formula Alpha => Call("of", V("true"));
    private static Formula Beta => Call("of", V("false"));
    private static Formula Pair(Formula x, Formula y) => Call("pair", x, y);
    private static Formula Spine(Formula a, Formula u) => Call("spine", a, u);
    private static Formula Cat(Formula a, Formula b) => Call("append", a, b);


    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original ordered-menu branch-first codes", H("Original ordered-menu branch-first codes"), Blocks(
            Paragraph(Text("Addresses are finite Boolean lists, with false denoting L and true denoting R. The actual Source is FreeMagma Bool, with true denoting alpha and false denoting beta. Menu is a list in the fixed public order. Child selection removes one matching leading bit and preserves that order. Repetition changes no rank rule; no lexicographic sorting occurs.")),
            Paragraph(Text("For a nonempty menu eta is zero exactly when every selected target has the form Lr with nonempty r. Empty menus have count one and code zero. Write J(S)=N(SL)N(SR) and bit(eta(S)) for the Boolean indicator as a natural number. The equations below are exactly the branch-first count and rank. The beta overlap rank is the branch rank of pair(alpha,alpha).")),
            Paragraph(Text("The recursion decreases the sum of length(q)+1 over the menu. Its range bound is proved jointly over the two child menus. Strictly positive child counts make the mixed-radix digits injective. A nonempty menu separates alpha and beta even in the overlap case: alpha has the outer leaf tag, while the overlap beta rank lies strictly inside the branch interval.")),
            Describe.Lean(DescribeId.Create("mem-child"), DeclarationHandle.Create(Prefix + "mem_child"), H("Ordered child membership"), StatementSource.FromAuthor(Disp(All("b",V("Bool"),All("S",V("Menu"),All("r",V("Address"),IffOf(Mem(V("r"),Call("child",V("b"),V("S"))),Mem(Call("cons",V("b"),V("r")),V("S")))))))), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Filtering matching heads is equivalent to membership of the original address with that head. This identity connects recursive reconstruction and path-context propagation to the same menu."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("original-code-grammar"), DeclarationHandle.Create(Prefix + "original_code_grammar"), H("Exact grammar and all-source range"), StatementSource.FromAuthor(Disp(All("S",V("Menu"),And(Imp(EqOf(V("S"),Nil),And(EqOf(Number(V("S")),D(1)),All("u",V("Source"),EqOf(Rank(V("S"),V("u")),D(0))))),Imp(NeOf(V("S"),Nil),And(EqOf(Number(V("S")),Add(Add(J(V("S")),D(1)),Call("bit",Call("eta",V("S"))))),All("x,y",V("Source"),EqOf(Rank(V("S"),Pair(V("x"),V("y"))),Add(Mul(Rank(Left(V("S")),V("x")),Number(Right(V("S")))),Rank(Right(V("S")),V("y"))))),EqOf(Rank(V("S"),Alpha),J(V("S"))),EqOf(Rank(V("S"),Beta),Call("if",Call("eta",V("S")),Add(J(V("S")),D(1)),Add(Mul(Rank(Left(V("S")),Alpha),Number(Right(V("S")))),Rank(Right(V("S")),Alpha)))))),Less(D(0),Number(V("S"))),All("u",V("Source"),Less(Rank(V("S"),V("u")),Number(V("S")))))))), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Branch ranks occupy the product interval. Alpha follows that interval, and beta follows alpha when eta is one. When eta is zero beta takes the specified branch rank. The range proof includes arbitrary actual trees, empty menus, epsilon and nested targets."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-code-context-separation"), DeclarationHandle.Create(Prefix + "original_code_context_separation"), H("One actual context preserves the rank distinction"), StatementSource.FromAuthor(Disp(All("S",V("Menu"),All("a,r",V("Address"),Imp(Mem(Cat(V("a"),V("r")),V("S")),NeOf(Rank(V("S"),Spine(V("a"),Alpha)),Rank(V("S"),Spine(V("a"),Beta)))))))), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The FM.21 context puts alpha at each side sibling and the chosen tree at address a. A selected extension makes the residual menu nonempty. The leaf distinction at the hole propagates through each branch digit using positive radices and cancellation. The same two trees are used by the future-vector obstruction."))), DescribeRole.Theorem))));
}
