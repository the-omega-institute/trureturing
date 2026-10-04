using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class FixedScalarFiberDiscoveryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed Fibonacci scalar fiber has two actual positive trees and sharp discovery costs.",
        H("Discovery on a Fixed Scalar Fiber"), Blocks(
            Paragraph(Text("Sources are nonempty finite free ordered full binary trees with alpha and beta leaves. "
                + "The original substitution rho sends alpha to beta and beta to pair(beta,alpha). "
                + "Every observation uses the original complete source through the four-valued address readout. "
                + "False denotes left and true denotes right. No associativity or commutativity quotient is used.")),
            Def("scalarFiber", "Complete scalar fiber", "For natural L put f=F(3L+3), g=F(3L+4), and m=3f+5g. "
                + "X(L) contains every source U with f times a(U) plus g times b(U) equal to m. "
                + "No image, composition, shape, leaf-count or height promise is supplied."),
            Def("P", "First positive source", "A=pair(pair(beta,alpha),beta), B=pair(A,pair(beta,alpha)), "
                + "and P=pair(A,B)=rho^3(pair(alpha,beta)). The blocks are the existing literal A and C."),
            Def("Q", "Second positive source", "Q=pair(B,A)=rho^3(pair(beta,alpha))."),
            Def("certificateSize", "Positive certificate cardinality", "k(L)=5 at L=0 and k(L)=3 at positive L."),
            Def("CorrectOn", "Pointwise fiber contract", "A history-only Policy pi is correct on X(L) "
                + "when every U in X(L) has a finite fuel-bounded execute run returning its actual third-image membership bit."),
            Def("WindowOn", "Observation window", "Every address in a terminating run on a source in X(L) "
                + "has length at most h. Together with CorrectOn this covers every actual query on each fiber input."),
            Def("NoRepeatOn", "Distinct queries", "The address list of every terminating run on X(L) is duplicate-free."),
            Def("discoveryCost", "Optimal worst-input cost", "C(pi,U) is extendedCost: the number of distinct "
                + "addresses in a finite run, and positive infinity for nontermination. D(L,h) is the infimum, "
                + "over policies correct on X(L) and obeying h, of the supremum of C over X(L)."),
            Def("certificate", "The two minimum certificates", "K(L,V) is the set of beta leaf addresses of V at L=0, "
                + "and its alpha address set at positive L."),
            Def("FiberSound", "Whole-fiber soundness", "A finite address set J is sound at V if every U in X(L) "
                + "matching V at all addresses in J is an actual third image."),
            Def("testNext", "Ordered endpoint test", "T(label,S) queries the listed addresses in left-right lexicographic order. "
                + "A matching leaf reply continues the test; all three other replies reject. Exhausting the list accepts."),
            Def("strategy", "The two complete response tables", "piP=strategy(L,true) and piQ=strategy(L,false). "
                + "At L=0 piP first queries LR: beta tests BP without LR, branch tests BQ, alpha and absent reject. "
                + "piQ first queries RR: beta tests BQ without RR, branch tests BP, alpha and absent reject. "
                + "At positive L piP first queries LLR: alpha tests AP without LLR, beta tests AQ, branch and absent reject. "
                + "piQ first queries RLR: alpha tests AQ without RLR, beta tests AP, branch and absent reject. "
                + "AP={LLR,RLLR,RRR}, AQ={LLLR,LRR,RLR}, BP={LLL,LR,RLLL,RLR,RRL}, "
                + "and BQ={LLLL,LLR,LRL,RLL,RR}. Every remaining test uses its corresponding leaf label."),
            Describe.Lean(DescribeId.Create("fixed-scalar-fiber-discovery-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Classification and Sharp Discovery Cost"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("L and h are natural numbers. Pi(L,h) denotes the policies satisfying CorrectOn(L) "
                        + "and WindowOn(L,h); I3 denotes the actual third substitution image. The scalar and all replies "
                        + "come from the same original source. Controller computation, scalar acquisition and address text length are free.")),
                    Paragraph(Text("Adjacent Fibonacci coefficients are coprime. Nonnegativity leaves four compositions "
                        + "at stage zero and only (3,5) later. Actual composition transport forces a positive source's "
                        + "preimage to have one leaf of each label, giving precisely P and Q. Each composition fiber is finite.")),
                    Paragraph(Text("At stage zero the five beta responses force the branching skeleton and beta slots. "
                        + "The three remaining subtrees have scalar sum six and each contributes at least two, "
                        + "so all three are single alpha leaves. Label exchanges and beta grafts establish the unique minimum beta certificate. "
                        + "At positive stages the alpha certificate theorem applies on the whole scalar fiber.")),
                    Paragraph(Text("Every accepting run is a sound certificate: any source matching its paid addresses "
                        + "follows the same deterministic history. The unique minimum certificates of P and Q are disjoint, "
                        + "but both runs share their first query. Their costs therefore cannot both be k(L). "
                        + "The two response tables attain the resulting bound and use only distinct addresses of depth at most four."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Def(string selector, string title, string text) =>
        Describe.Lean(DescribeId.Create("fixed-scalar-" + selector.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + selector), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Definition);
    private static Formula Set(params Formula[] xs) => new Formula.SetLiteral([.. xs]);
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula f) => Seq(Open,f,Close);
    private static Formula Call(string s, params Formula[] xs) =>
        new Formula.Apply(Seq(Operatorname,Grp(V(s))),[.. xs]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula LeOf(Formula a, Formula b) => Seq(a,Sp,Leq,Sp,b);
    private static Formula And(params Formula[] xs) => Seq(xs.Select((x,i) =>
        i == 0 ? Par(x) : Seq(Sp,Land,Sp,Par(x))).ToArray());
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a),Sp,Implies,Sp,Par(b));
    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall,Sp,V(x),Sp,InMacro,Sp,type,Comma,Sp,Par(body));
    private static Formula ResultFormula()
    {
        var l=V("L"); var h=V("h"); var k=Call("k",l); var pi=V("pi");
        var p=V("P"); var q=V("Q"); var x=Call("X",l);
        var cp=Call("C",pi,p); var cq=Call("C",pi,q);
        var lawful=Call("Pi",l,h);
        var compositions=Call("if",EqOf(l,Num(0)),
            Set(Call("pair",Num(0),Num(7)),Call("pair",Num(3),Num(5)),
                Call("pair",Num(6),Num(3)),Call("pair",Num(9),Num(1))),Set(Call("pair",Num(3),Num(5))));
        var lower=All("pi",lawful,And(LeOf(k,cp),LeOf(k,cq),
            LeOf(Seq(Num(2),Sp,k,Sp,Plus,Sp,Num(1)),Seq(cp,Sp,Plus,Sp,cq))));
        var upper=And(Call("CorrectOn",l,V("piP")),Call("CorrectOn",l,V("piQ")),
            Call("WindowOn",l,Num(4),V("piP")),Call("WindowOn",l,Num(4),V("piQ")),
            Call("NoRepeatOn",l,V("piP")),Call("NoRepeatOn",l,V("piQ")),
            All("U",x,And(LeOf(Call("C",V("piP"),V("U")),Seq(k,Sp,Plus,Sp,Num(1))),
                LeOf(Call("C",V("piQ"),V("U")),Seq(k,Sp,Plus,Sp,Num(1))))),
            EqOf(Call("pair",Call("C",V("piP"),p),Call("C",V("piP"),q)),Call("pair",k,Seq(k,Sp,Plus,Sp,Num(1)))),
            EqOf(Call("pair",Call("C",V("piQ"),p),Call("C",V("piQ"),q)),Call("pair",Seq(k,Sp,Plus,Sp,Num(1)),k)));
        var value=Call("if",Seq(h,Sp,Lt,Sp,Num(4)),Infty,
            Call("if",EqOf(l,Num(0)),Num(6),Num(4)));
        return All("L",V("Nat"),All("h",V("Nat"),And(Call("Finite",x),
            EqOf(Call("c",x),compositions),EqOf(Call("inter",x,V("I3")),Set(p,q)),
            Seq(p,Sp,Neq,Sp,q),EqOf(p,Call("rho3",Call("pair",V("alpha"),V("beta")))),
            EqOf(q,Call("rho3",Call("pair",V("beta"),V("alpha")))),
            Imp(Seq(h,Sp,Lt,Sp,Num(4)),EqOf(lawful,Emptyset)),
            Imp(LeOf(Num(4),h),And(lower,upper)),EqOf(Call("D",l,h),value))));
    }
}
