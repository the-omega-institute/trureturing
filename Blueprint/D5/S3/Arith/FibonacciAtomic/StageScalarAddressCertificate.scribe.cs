using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class StageScalarAddressCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/StageScalarAddressCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One known Fibonacci scalar stage determines the exact price of certifying an actual ordered tree image.",
        H("Scalar Stage Address Certificates"), Blocks(
            Paragraph(Text("Source is the existing nonempty finite ordered full binary tree algebra. "
                + "The substitution rho sends alpha to beta and beta to pair(beta,alpha), and preserves ordered pairing. "
                + "I(d) is the range of its d-fold iterate. A(V) and B(V) are the literal alpha and beta leaf-address sets of V; "
                + "a(V) and b(V) are their cardinalities. D(V) is maximum leaf depth, with root depth zero. "
                + "For natural L, f(L)=F(3L+3) and g(L)=F(3L+4), with F(0)=0 and F(1)=1. "
                + "Write t(V,L)=max(0,b(V)+1-f(L)) and M(V,L)=min(b(V),a(V)+t(V,L)). "
                + "S(f,g,d,V,h,Q) is QuantityAddressCertificate.ScalarSound: all queries in the finite set Q have depth at most h, "
                + "and every complete U with f*a(U)+g*b(U)=f*a(V)+g*b(V) and matching raw replies on Q belongs to I(d). "
                + "The scalar and replies refer to the same original tree. Competitor shape, composition, leaf count and height are unrestricted. "
                + "Queries may include roots, branches or absent addresses and need not be closed under prefixes.")),
            Describe.Lean(DescribeId.Create("stage-scalar-address-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Exact minimum and every attaining set"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every natural k at least one, every natural L, every V in I(3k) and every natural h, "
                        + "b(V)>a(V)>=1. Below D(V) there is no sound query set. At or above D(V), every sound set has at least M(V,L) queries, "
                        + "some sound set has exactly that many, and the displayed equivalence lists all such sets. "
                        + "They are B(V), when b(V)=M(V,L), and A(V) union C, where C is a subset of B(V) with cardinality t(V,L), "
                        + "when a(V)+t(V,L)=M(V,L). Thus a minimum set contains only original leaf addresses. "
                        + "The four price intervals are f<=a, f=a+1, a+1<f<=b and b<f, giving respectively b, b, a+b+1-f and a. "
                        + "For fixed V and h>=D(V), the price is nonincreasing in L and equals a at all sufficiently large stages. "
                        + "The two global scalar equivalence kernels at stages zero and one do not contain each other. "
                        + "Here n0(U)=2*a(U)+3*b(U) and n1(U)=8*a(U)+13*b(U); cut(x,y)=max(0,x-y).")),
                    Paragraph(Text("Matching all beta endpoints fixes the branch skeleton. Positive weights f<g<2f make alpha "
                        + "the unique minimum-weight replacement of each remaining alpha slot, so the scalar equality reconstructs V. "
                        + "Matching all alpha endpoints and t beta endpoints also reconstructs V: consecutive Fibonacci weights are coprime, "
                        + "and the remaining possible beta deficit is smaller than f, forcing that deficit to vanish.")),
                    Paragraph(Text("If both an alpha and a beta endpoint are omitted, the existing composition-preserving exchange "
                        + "produces an image-negative tree matching all queries. Hence soundness requires all alpha or all beta endpoints. "
                        + "Put p=F(3L+2), q=F(3L+1), so f=p+q and g=2p+q, with p,q positive. "
                        + "For any two disjoint sets X,Y of original beta leaves, simultaneous relabeling at X and expansion to pair(alpha,alpha) at Y "
                        + "produces a legal complete tree. Its composition changes by (card(X)+2*card(Y),-card(X)-card(Y)). "
                        + "Its exact reply-change support consists of X, Y and the two immediate children of each member of Y. "
                        + "A nonempty Y supplies a left alpha child, excluding the tree from the actual image.")),
                    Paragraph(Text("If at least f beta endpoints are omitted and at least p of them have neither immediate child queried, "
                        + "choose p of those for Y and q other omitted endpoints for X. The batch preserves the scalar and every queried reply, "
                        + "contradicting soundness. Therefore fewer than p omitted slots are unblocked. Distinct blocked slots consume distinct "
                        + "queried child addresses outside the original leaves. This gives a strict excess over a(V)+t(V,L). "
                        + "When fewer than f beta endpoints are omitted, the elementary cardinality bound is a(V)+t(V,L), "
                        + "with equality precisely for the stated alpha-plus-beta subsets. "
                        + "Fibonacci monotonicity gives price monotonicity, and the unbounded Fibonacci lower bound eventually makes t zero. "
                        + "Actual trees of compositions (3,0) and (0,2) agree under n0 but disagree under n1. "
                        + "Actual trees of compositions (13,0) and (0,8) agree under n1 but disagree under n0."))), DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] xs) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. xs]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LeOf(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula And(params Formula[] xs) => Seq(xs.Select((x,i) =>
        i == 0 ? Par(x) : Seq(Sp, Land, Sp, Par(x))).ToArray());
    private static Formula All(string x, Formula domain, Formula body) =>
        Seq(Forall, Sp, V(x), Sp, InMacro, Sp, domain, Comma, Sp, Par(body));
    private static Formula ExistsIn(string x, Formula domain, Formula body) =>
        Seq(F.Exists, Sp, V(x), Sp, InMacro, Sp, domain, Comma, Sp, Par(body));
    private static Formula ResultFormula()
    {
        Formula k=V("k"), l=V("L"), v=V("V"), h=V("h"), q=V("Q"), c=V("C");
        Formula d=Seq(D(3),Sp,Cdot,Sp,k), a=Call("a",v), b=Call("b",v), beta=Call("B",v);
        Formula t=Call("t",v,l), m=Call("M",v,l), sets=Call("Finset",V("Address"));
        Formula S(Formula query) => Call("S",Call("f",l),Call("g",l),d,v,h,query);
        Formula choice=Seq(Par(And(EqOf(q,beta),EqOf(b,m))),Sp,Lor,Sp,
            Par(ExistsIn("C",sets,And(Seq(c,Sp,Subseteq,Sp,beta),EqOf(Call("card",c),t),
                EqOf(q,Seq(Call("A",v),Sp,Cup,Sp,c)),EqOf(Seq(a,Sp,Plus,Sp,t),m)))));
        Formula frontier=Imp(LeOf(Call("D",v),h),And(
            All("Q",sets,Imp(S(q),LeOf(m,Call("card",q)))),
            All("Q",sets,Seq(Par(And(S(q),EqOf(Call("card",q),m))),Sp,Leftrightarrow,Sp,Par(choice))),
            ExistsIn("Q",sets,And(S(q),EqOf(Call("card",q),m)))));
        Formula f=Call("f",l), lp=V("Lprime"), l0=V("Lzero"), u=V("U"), w=V("W");
        Formula cases=And(Imp(LeOf(f,a),EqOf(m,b)),
            Imp(EqOf(f,Seq(a,Sp,Plus,Sp,D(1))),EqOf(m,b)),
            Imp(Seq(a,Sp,Plus,Sp,D(1),Sp,Lt,Sp,f),Imp(LeOf(f,b),
                EqOf(m,Call("cut",Seq(a,Sp,Plus,Sp,b,Sp,Plus,Sp,D(1)),f)))),
            Imp(Seq(b,Sp,Lt,Sp,f),EqOf(m,a)));
        Formula monotone=All("Lprime",V("Nat"),Imp(LeOf(l,lp),LeOf(Call("M",v,lp),m)));
        Formula eventual=ExistsIn("Lzero",V("Nat"),All("Lprime",V("Nat"),
            Imp(LeOf(l0,lp),EqOf(Call("M",v,lp),a))));
        Formula Noninclusion(string first, string second) => Seq(Neg,Sp,
            Par(All("U",V("Source"),All("W",V("Source"),
                Imp(EqOf(Call(first,u),Call(first,w)),EqOf(Call(second,u),Call(second,w)))))));
        return Disp(All("k",V("Nat"),Imp(LeOf(D(1),k),All("L",V("Nat"),All("V",V("Source"),
            Imp(Seq(v,Sp,InMacro,Sp,Call("I",d)),All("h",V("Nat"),And(
                LeOf(D(1),a),Seq(a,Sp,Lt,Sp,b),
                Imp(Seq(h,Sp,Lt,Sp,Call("D",v)),Seq(Neg,Sp,ExistsIn("Q",sets,S(q)))),
                frontier,cases,monotone,eventual,Noninclusion("n0","n1"),Noninclusion("n1","n0")))))))));
    }
}
