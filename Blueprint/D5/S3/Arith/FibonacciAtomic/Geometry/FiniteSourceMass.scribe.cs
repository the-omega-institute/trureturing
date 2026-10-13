using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class FiniteSourceMassDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original guarded address geometry and uniform all-occurrence cylinder masses.", H("Actual Fibonacci Descendant Masses"), Blocks(
            Def("vertices", "vertices(n) contains every original occurrence address of T(n), with the root included."),
            Def("N", "N(n) is the cardinality of vertices(n)."),
            Def("Node", "Node(n) is the subtype of actual occurrence addresses of T(n)."),
            Def("μ", "mu(n) is the uniform probability measure on Node(n); it assigns equal mass to roots, branches and both terminal labels."),
            Def("descendants", "descendants(n,p) filters vertices(n) by the original prefix relation."),
            Def("mass", "mass(n,p) is the cardinality of descendants(n,p) divided by N(n)."),
            Def("a", "a is the reciprocal of the real golden ratio."),
            Describe.Lean(DescribeId.Create("finitesourcemass-result"),
                DeclarationHandle.Create(Prefix + "finite_source_masses"), H("Actual Fibonacci Descendant Masses"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("False denotes a left edge and true denotes a right edge. The inherited pathCost adds one for left and two for right. dropLast removes the final edge. A descent is permitted only from a branch, so both the final cost and the last-parent cost plus two must be at most n.")),
                    Paragraph(Text("In the formula, label(d) is alpha for d=0, beta for d=1 and branch for d>=2. descendantMeasure(n,p) denotes the real value of mu(n) on the actual nodes whose addresses extend p. pointMeasure(n,x) is the extended nonnegative point mass of x. These quantities use all occurrences, including internal nodes and the root.")),
                    Paragraph(Text("The guarded native navigation identifies the entire residual source at each reached address. Prefixing its node enumeration gives the actual ambient descendant set. The original node count is twice the Fibonacci leaf count minus one. Its recurrence yields golden-ratio upper and lower bounds, and their ratio gives the uniform envelope. An absent prefix has no descendants. A terminal cannot be crossed by a further nonempty suffix.")),
                    Paragraph(Text("The two singleton sources are retained: the root is alpha at n=0 and beta at n=1. Both have total mass one."))), DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string prose) => Describe.Lean(
        DescribeId.Create("finitesourcemass-" + (name == "μ" ? "mu" : name.ToLowerInvariant())),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula All(string s, Formula t, Formula x) => Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp, Par(x));
    private static Formula Ex(string s, Formula t, Formula x) => Seq(Exists, Sp, V(s), Colon, Sp, t, Comma, Sp, Par(x));
    private static Formula EqOf(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula LeOf(Formula x, Formula y) => Seq(x, Sp, Leq, Sp, y);
    private static Formula NeOf(Formula x, Formula y) => Seq(x, Sp, Neq, Sp, y);
    private static Formula Imp(Formula x, Formula y) => Seq(Par(x), Sp, Implies, Sp, Par(y));
    private static Formula IffOf(Formula x, Formula y) => Seq(Par(x), Sp, Iff, Sp, Par(y));
    private static Formula And(Formula x, Formula y) => Seq(Par(x), Sp, Land, Sp, Par(y));
    private static Formula Add(Formula x, Formula y) => Seq(Par(x), Sp, Plus, Sp, Par(y));
    private static Formula Sub(Formula x, Formula y) => Seq(Par(x), Sp, Minus, Sp, Par(y));
    private static Formula Mul(Formula x, Formula y) => Seq(Par(x), Sp, Cdot, Sp, Par(y));
    private static Formula Div(Formula x, Formula y) => Seq(Frac, Grp(x), Grp(y));
    private static Formula Pow(Formula x, Formula y) => Seq(Par(x), Caret, Grp(y));
    private static Formula NatType => Seq(Mathbb, Grp(V("N")));
    private static Formula Nil => Seq(OpenBracket, CloseBracket);
    private static Formula Conj(params Formula[] xs) => xs.Aggregate(And);
    private static Formula Bounds(string[] names, Formula[] types, Formula body)
    {
        for (int i=names.Length-1; i>=0; --i) body=All(names[i], types[i], body);
        return body;
    }
    private static Formula ResultFormula()
    {
        Formula n=V("n"), p=V("p"), u=V("U"), x=V("x"), b=V("b"), q=V("q");
        Formula addr=Call("Address"), src=Call("Source"), cost=Call("pathCost",p);
        Formula d=Sub(n,cost), tree=Call("T",n), st=Call("subtree",p,tree);
        Formula reached=Ex("U",src,EqOf(st,Call("some",u)));
        Formula valid=And(LeOf(cost,n),LeOf(Add(Call("pathCost",Call("dropLast",p)),D(2)),n));
        Formula c=Mul(Mul(D(2),Call("goldenRatio")),Pow(V("a"),Call("length",p)));
        Formula f1=Bounds(["n","p"],[NatType,addr],Imp(NeOf(p,Nil),IffOf(reached,valid)));
        Formula f2=Bounds(["n","p"],[NatType,addr],Imp(NeOf(p,Nil),Imp(LeOf(cost,n),
            Imp(LeOf(Add(Call("pathCost",Call("dropLast",p)),D(2)),n),And(
                EqOf(st,Call("some",Call("T",d))),
                EqOf(Call("mass",n,p),Div(Call("N",d),Call("N",n))))))));
        Formula f3=Bounds(["n","p"],[NatType,addr],Imp(EqOf(st,Call("none")),EqOf(Call("mass",n,p),D(0))));
        Formula f4=Bounds(["n","p"],[NatType,addr],LeOf(Call("mass",n,p),c));
        Formula f5=Bounds(["n","p"],[NatType,addr],EqOf(Call("descendantMeasure",n,p),Call("mass",n,p)));
        Formula f6=All("n",NatType,All("x",Call("Node",n),EqOf(Call("pointMeasure",n,x),Div(D(1),Call("N",n)))));
        Formula f7=Bounds(["n","p"],[NatType,addr],Imp(EqOf(st,Call("some",Call("T",d))),
            EqOf(Call("readout",p,tree),Call("label",d))));
        Formula f8=Bounds(["n","p","b"],[NatType,addr,Call("Bool")],
            Imp(EqOf(st,Call("some",Call("of",b))),All("q",addr,Imp(NeOf(q,Nil),
                EqOf(Call("subtree",Call("append",p,q),tree),Call("none"))))));
        Formula f9=All("n",NatType,And(EqOf(Call("mass",n,Nil),D(1)),
            EqOf(Call("readout",Nil,tree),Call("label",n))));
        return Conj(f1,f2,f3,f4,f5,f6,f7,f8,f9);
    }
}
