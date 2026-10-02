using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class GenealogicalFiberTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered tree shapes and their leaf labels determine exact composition fibers.",
        H("Composition Fibers and Fibonacci Genealogical Transport"),
        Blocks(
            Paragraph(Text("Sources are nonempty ordered full binary trees. True labels alpha and false labels beta. "
                + "Their composition counts the two leaf labels. The Fibonacci step and quantity are "
                + "M(a,b)=(b,a+b) and q(a,b)=2a+3b.")),
            Def("Source", "Actual sources", "The source type is FreeMagma Bool, with the original ordered tree constructors."),
            Def("substitution", "Native substitution", "The magma homomorphism sends alpha to beta and beta to the ordered pair (beta,alpha)."),
            Def("composition", "Actual leaf composition", "Alpha has composition (1,0), beta has composition (0,1), and pairing adds compositions."),
            Def("Fiber", "Composition fiber", "Fiber(v) consists of actual source trees whose composition equals v."),
            Def("fiberCount", "Catalan and binomial expression", "N(a,b)=catalan(a+b-1) choose(a+b,a). Natural subtraction is truncated at zero."),
            Def("TreeLabels", "Labels on a shape", "A leaf carries one Boolean label, and an internal node carries the labels of its left and right subshapes."),
            Def("assemble", "Assembling a source", "Assembling a shape with its leaf labels produces the actual ordered source tree."),
            Def("decompose", "Decomposing a source", "Decomposition retains the ordered shape and every leaf label."),
            Def("sourceEquiv", "Shape and label equivalence", "Assembly and decomposition are inverse on all nonempty ordered sources."),
            Def("labelsEquiv", "Indexed leaf labels", "Leaf labels are functions on the left-to-right leaf positions of a shape."),
            Def("indexedEquiv", "Complete indexed encoding", "An actual source corresponds to its ordered shape and its Boolean leaf-position function."),
            Def("positionedEquiv", "Shape and alpha positions", "An actual source corresponds to its ordered shape and the subset of its alpha positions, using the existing supportEquiv."),
            Def("fiberEquiv", "Fixed-composition correspondence", "For a+b>=1, actual sources of composition (a,b) correspond to shapes with a+b-1 internal nodes and subsets of exactly a alpha positions."),
            Def("fiberMap", "Actual iterated substitution", "The map from Fiber(v) to Fiber(M^n v) sends a source to its n-th substituted tree."),
            Def("uniformMass", "Real uniform mass", "Each tree in a nonempty fiber has mass 1/card(Fiber(v))."),
            Def("transportVariation", "Variation on one target fiber", "Compare the actual pushforward and the uniform target mass using one half of their finite absolute-difference sum."),
            Describe.Lean(DescribeId.Create("genealogical-fiber-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Exact hidden fibers and transport variation"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("All a,b,n are natural numbers, including zero. F(v) is the actual tree fiber, "
                        + "N(v) its Catalan and binomial expression, P_n(v,y) the existing preimage-sum pushforward applied to the actual fiber map and source uniform mass, and U(v,y) "
                        + "the uniform mass. M(n,v) denotes M^n v and rho(n,t) denotes rho^n t. TV(v,n) compares the pushed and uniform target masses. I_n(v) is the image of the actual fiber map rho_v^n. Every sum below "
                        + "ranges over the whole target fiber F(M^n v).")),
                    Paragraph(Text("The substitution is injective because no image is the leaf alpha. The image of a beta leaf "
                        + "is the pair (beta,alpha), which cannot be the image of an internal node: its right child alpha "
                        + "is not an image. The remaining pairs decode recursively. Thus each positive pushforward mass "
                        + "has exactly one preimage, and the image has the cardinality of the source fiber.")),
                    Paragraph(Text("The total variation splits into the image and its complement. The image contributes "
                        + "the difference between the reciprocal source and target cardinalities; the complement "
                        + "contributes the reciprocal target cardinality. The one-step bound follows from Catalan "
                        + "doubling after index one and monotonicity of the binomial coefficient. Under iteration, "
                        + "the total leaf count increases by at least one every two steps, and the target cardinality "
                        + "grows without bound. Its reciprocal tends to zero."))), DescribeRole.Theorem),
            Paragraph(Text("The shape count is the Catalan count in Stanley, Enumerative Combinatorics, Volume 2, section 6.2. "
                + "The shape enumeration and the finite subset count use their corresponding mathlib results.")))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("genealogical-fiber-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Pair(Formula a, Formula b) => Par(Seq(a, Comma, Sp, b));
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LeOf(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Fraction(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Pow(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula And(params Formula[] xs)
    {
        var fs = new List<Formula>();
        for (int i = 0; i < xs.Length; i++)
        {
            if (i > 0) fs.Add(Seq(Sp, Land, Sp, RowBreak, Grp()));
            fs.Add(Par(xs[i]));
        }
        return Seq(fs.ToArray());
    }
    private static Formula All(string vars, Formula f) => Seq(Forall, Sp,
        Seq(vars.Split(',').Select((s,i) => i == 0 ? V(s) : Seq(Comma, Sp, V(s))).ToArray()), Comma, Sp, Par(f));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula InOf(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Fiber(Formula v) => Call("F", v);
    private static Formula N(Formula v) => Call("N", v);
    private static Formula M(Formula n, Formula v) => Call("M", n, v);
    private static Formula Rho(Formula n, Formula t) => Call("rho", n, t);
    private static Formula Tv(Formula v, Formula n) => Call("TV", v, n);
    private static Formula TargetSum(Formula f, Formula v, Formula n) => Seq(Sum, Underscore,
        Grp(InOf(V("y"), Fiber(M(n,v)))), Sp, f);
    private static Formula ResultFormula()
    {
        Formula a=V("a"), b=V("b"), n=V("n"), t=V("t"), y=V("y"), v=Pair(a,b);
        Formula composition=EqOf(Call("c",Rho(n,t)),M(n,v));
        Formula quantity=EqOf(Call("q",Call("c",Rho(n,t))),Call("q",M(n,v)));
        Formula trajectory=All("t",Imp(InOf(t,Fiber(v)),All("n",And(composition,quantity))));
        Formula pn=Call("P",n,v,y), un=Call("U",M(n,v),y);
        Formula transport=All("n",And(Call("Injective",Call("rhoFiber",v,n)),
            EqOf(Call("card",Call("I",n,v)),N(v)),
            All("y",Imp(InOf(y,Fiber(M(n,v))),And(LeOf(D(0),pn),LeOf(D(0),un)))),
            EqOf(TargetSum(pn,v,n),D(1)),EqOf(TargetSum(un,v,n),D(1)),
            EqOf(Tv(v,n),Sub(D(1),Fraction(N(v),N(M(n,v)))))));
        Formula lower=Imp(LeOf(D(2),Add(a,b)),LeOf(Sub(D(1),Pow(Fraction(D(1),D(2)),b)),Tv(v,D(1))));
        Formula limit=Call("Tendsto",Seq(n,Sp,Mapsto,Sp,Tv(v,n)),V("atTop"),Call("nhds",D(1)));
        Formula conclusion = And(All("a,b",Imp(LeOf(D(1),Add(a,b)),And(Call("Finite",Fiber(v)),
            EqOf(Call("card",Fiber(v)),N(v)),Call("Nonempty",Fiber(v)),trajectory,transport,lower,limit))),
            EqOf(Tv(Pair(D(1),D(1)),D(1)),Fraction(D(2),D(3))));
        return Disp(Seq(Begin, Grp(V("gathered")), conclusion, End, Grp(V("gathered"))));
    }

}
