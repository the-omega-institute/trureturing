using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers.BipartiteBlockade;

internal sealed class StrictBornFibersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict Born sources in the unresolved fiber of a single positive drive.",
        H("Interior five-mode ambiguities at every scale"),
        Blocks(Describe.Lean(
            DescribeId.Create("strict-born-single-setting-fiber"),
            DeclarationHandle.Create("D5/S3/Quantum/Fibers/BipartiteBlockade/StrictBornFibers.strict_born_single_setting_fiber"),
            H("An actual joint endpoint probability changes in the open pyramid"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let G be a finite connected simple graph with a proper Boolean coloring, "
                    + "maximum degree at most two, and at least two distinct open neighborhoods "
                    + "of cardinality at least two. Fix any strictly positive drive Ω and any "
                    + "positive radius r. The theorem produces actual complex density matrices "
                    + "ρ and σ indexed by the independent sets of G. Both matrices are positive "
                    + "definite and have complex trace one. The C-star norm of each matrix minus "
                    + "the maximally mixed matrix is strictly smaller than r.")),
                Paragraph(Text(
                    "Every vertex occupation and every acceleration obtained from the actual "
                    + "legal-flip Hamiltonian agree between ρ and σ. For every degree-two center "
                    + "v with two distinct neighbors u,w, all five masses of both Born diagonal "
                    + "marginals are strictly positive. The mode order is vacuum, left endpoint, "
                    + "center, right endpoint, and both endpoints. At some such center the joint "
                    + "endpoint mass, mode four, differs between the two states. Define the task f(k) "
                    + "as the product of the endpoint occupation indicators: the first is one on "
                    + "modes one and four, and the second on modes three and four. The theorem "
                    + "also proves f(4)−f(1)−f(3)+f(0)=1 and that the two actual Born task "
                    + "expectations differ. The actual hidden association coordinate Δ=(1−Z)κ−XY "
                    + "also differs, with κ the same Born joint endpoint mass. BornTaskExpectation in the displayed statement is the "
                    + "finite sum over k in Fin 5 of bornModeLaw(G,u,v,w,ρ,k) times endpointTask(k).")),
                Paragraph(Text(
                    "For that center write X=m_u, Y=m_w and Z=m_v. Each state's center complement "
                    + "1−Z is strictly positive, and its width min{X,Y,1−Z−X,1−Z−Y} is strictly "
                    + "positive. The width is the minimum of four boundary distances. The proof "
                    + "uses the existing five-mode global chart: the strictly positive Born law "
                    + "has total mass one and its visible point is exactly (X,Y,Z), so it lies "
                    + "in the open square pyramid. In the displayed statement, twoDistinctNeighbors(G,u,v,w) "
                    + "means u≠w and, for every x, G.Adj(v,x) if and only if x=u or x=w.")),
                Paragraph(Text(
                    "The construction consumes the sharp five-mode setting-number classification. "
                    + "If a single prescribed positive drive were sufficient, its feasible count "
                    + "would force the minimum to be at most one, contradicting d≥2. Its failure "
                    + "supplies positive semidefinite normalized states P,Q with equal source "
                    + "data and different five-mode laws. Their Hermitian traceless difference "
                    + "R=P−Q preserves the data. Opposite sufficiently small real multiples of R "
                    + "about the maximally mixed state give the required strictly positive states. "
                    + "The five-mode reconstruction formula transfers their changed blockade "
                    + "coordinate to their changed joint endpoint mass.")),
                Paragraph(Text(
                    "This concerns repeated preparation of one unknown initial state and occupation "
                    + "plus second-derivative data. The conclusion provides actual Born sources "
                    + "with an unresolved joint endpoint task. It does not assert a native Fibonacci "
                    + "continuation, equality of higher derivatives, or a finite-sampling error bound."))),
            DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, V(x), Colon, type, Comma, Sp, body, Close);
    private static Formula Conj(params Formula[] parts)
    {
        var items = new List<Formula>();
        for (var i = 0; i < parts.Length; i++)
        {
            if (i > 0) items.AddRange([Sp, Land, Sp]);
            items.Add(parts[i]);
        }
        return Seq([.. items]);
    }
    private static Formula E(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Positive(Formula a) => Seq(D(0), Sp, Lt, Sp, a);
    private static Formula Mean(Formula state, string x) => C("occupationMean", V("G"),state,V(x));
    private static Formula Law(Formula state, Formula k) => C("bornModeLaw", V("G"),V("u"),V("v"),V("w"),state,k);
    private static Formula Width(Formula state) => C("min",
        C("min",Mean(state,"u"),Mean(state,"w")),
        C("min",Seq(D(1),Minus,Mean(state,"v"),Minus,Mean(state,"u")),
            Seq(D(1),Minus,Mean(state,"v"),Minus,Mean(state,"w"))));
    private static Formula Delta(Formula state) => Seq(Open,D(1),Minus,Mean(state,"v"),Close,
        Law(state,D(4)),Minus,Mean(state,"u"),Mean(state,"w"));
    private static Formula Centers(Formula body) => All("u",V("V"),All("v",V("V"),All("w",V("V"),
        Seq(C("twoDistinctNeighbors",V("G"),V("u"),V("v"),V("w")),Rightarrow,Sp,body))));
    private static Formula Statement()
    {
        var g=V("G"); var r=V("ρ"); var s=V("σ");
        var matrix=C("Matrix",C("Configuration",g),C("Configuration",g),C("Complex"));
        var assumptions=Conj(C("Connected",g),C("ProperColoring",g,V("c")),
            All("v",V("V"),Positive(C("Ω",V("v")))),
            All("v",V("V"),Seq(C("card",C("neighborFinset",g,V("v"))),Sp,Le,Sp,D(2))),
            Seq(D(2),Sp,Le,Sp,C("card",C("nonlinearNeighborhoods",g))),Positive(V("r")));
        var witness=Seq(Exists,Sp,V("u"),Comma,V("v"),Comma,V("w"),Colon,V("V"),Comma,Sp,
            Conj(C("twoDistinctNeighbors",g,V("u"),V("v"),V("w")),
                Positive(Seq(D(1),Minus,Mean(r,"v"))),Positive(Seq(D(1),Minus,Mean(s,"v"))),
                Positive(Width(r)),Positive(Width(s)),Seq(Law(r,D(4)),Sp,Neq,Sp,Law(s,D(4))),
                E(Seq(C("endpointTask",D(4)),Minus,C("endpointTask",D(1)),Minus,
                    C("endpointTask",D(3)),Plus,C("endpointTask",D(0))),D(1)),
                Seq(C("BornTaskExpectation",g,V("u"),V("v"),V("w"),r,C("endpointTask")),Sp,Neq,Sp,
                    C("BornTaskExpectation",g,V("u"),V("v"),V("w"),s,C("endpointTask"))),
                Seq(Delta(r),Sp,Neq,Sp,Delta(s))));
        var conclusion=Conj(C("PosDef",r),E(C("trace",r),D(1)),C("PosDef",s),E(C("trace",s),D(1)),
            Seq(C("norm",C("ofMatrix",Seq(r,Minus,C("maximallyMixed",g)))),Sp,Lt,Sp,V("r")),
            Seq(C("norm",C("ofMatrix",Seq(s,Minus,C("maximallyMixed",g)))),Sp,Lt,Sp,V("r")),
            All("v",V("V"),E(Mean(r,"v"),Mean(s,"v"))),
            All("v",V("V"),E(C("acceleration",g,V("Ω"),r,V("v")),C("acceleration",g,V("Ω"),s,V("v")))),
            Centers(All("k",C("Fin",D(5)),Conj(Positive(Law(r,V("k"))),Positive(Law(s,V("k")))))),witness);
        return Disp(Seq(Forall,Sp,V("V"),Colon,C("Type"),Comma,Sp,
            OpenBracket,C("Fintype",V("V")),CloseBracket,Comma,Sp,
            OpenBracket,C("DecidableEq",V("V")),CloseBracket,Comma,Sp,
            g,Colon,C("SimpleGraph",V("V")),Comma,Sp,
            V("c"),Colon,Seq(V("V"),To,C("Bool")),Comma,Sp,
            V("Ω"),Colon,Seq(V("V"),To,C("Real")),Comma,Sp,V("r"),Colon,C("Real"),Comma,Sp,
            assumptions,Rightarrow,Sp,Exists,Sp,r,Comma,s,Colon,matrix,Comma,Sp,conclusion,Dot));
    }
}
