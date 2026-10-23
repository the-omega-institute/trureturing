using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class AncestorAreaIntervalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInterval.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/loday2002stasheff");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An interval sum of native ancestor coordinates equals its binomial lower bound exactly at an actual complete subtree occurrence.",
        H("Ancestor Area and Complete Leaf Intervals"), Blocks(
            Paragraph(Text("Source is FreeMagma Bool, the existing nonempty ordered binary tree algebra. "
                + "Leaves are numbered from one in the actual left-to-right leaf-address enumeration. "
                + "False in an address means left and true means right. Labels need not be distinct, "
                + "and no substitution-image restriction is imposed.")),
            Def("coordinates", "Actual gap coordinates",
                "A leaf has the empty coordinate list. For pair(l,r), the list is coordinates(l), "
                + "followed by length(l)*length(r), followed by coordinates(r). Its entries are A(i) "
                + "at gaps i=1,...,length(t)-1: the root gap follows all left-child gaps, and its "
                + "coordinate is the product of the actual child leaf counts."),
            Def("area", "Consecutive gap sum",
                "area(t,a,b) is the sum of take(b-a,drop(a-1,coordinates(t))). Thus it is exactly "
                + "the sum of A(i) for i=a,...,b-1. At a=b the sum is empty and equals zero."),
            Def("offset", "Ambient position of an occurrence",
                "offset(t,u) counts leaves before the addressed subtree. The empty root address has "
                + "offset zero. A left step preserves the child offset; a right step adds the entire "
                + "left-child leaf count. Navigation past a leaf has no subtree and cannot satisfy "
                + "CompleteSubtree."),
            Def("CompleteSubtree", "Actual complete subtree interval",
                "CompleteSubtree(t,a,b) means that there are an actual address u and tree s with "
                + "subtree(u,t)=some(s), a=offset(t,u)+1, and b=offset(t,u)+length(s). In addition, "
                + "take(b-a+1,drop(a-1,leaves(t))) equals the list leaves(s) with u prefixed to every "
                + "address. This identifies every ambient leaf occurrence in order, rather than "
                + "only its label, subtree value, or cardinality."),
            Describe.Lean(DescribeId.Create("ancestor-area-interval"),
                DeclarationHandle.Create(Prefix + "ancestor_area_interval"),
                H("The Complete Interval Bound and Equality Criterion"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every Source tree and every 1<=a<=b<=length(t), put k=b-a+1. "
                        + "The ancestor-area sum is at least choose(k,2), with equality if and only if "
                        + "the interval consists of all leaves of an actual addressed subtree. "
                        + "This includes all prefixes, suffixes, singleton intervals, the full tree, "
                        + "and the one-leaf tree, regardless of repeated labels.")),
                    Paragraph(Text("Split the interval at the root gap. An interval contained in one "
                        + "child inherits that child's bound and subtree occurrence. For a crossing "
                        + "interval, let p,q be the child leaf counts and x,y the positive selected "
                        + "leaf counts on the two sides. The two child interval sums contribute at "
                        + "least choose(x,2) and choose(y,2), and the root contributes pq>=xy. "
                        + "The identity choose(x+y,2)=choose(x,2)+choose(y,2)+xy gives the bound. "
                        + "Equality implies pq=xy; since 0<x<=p and 0<y<=q, this forces x=p and "
                        + "y=q, so the interval is the root's whole leaf interval. Conversely the "
                        + "whole interval has equality by the same recurrence.")),
                    Paragraph(Text("Address navigation also gives the exact ambient ordered leaf slice "
                        + "of each occurrence. Left steps prefix false; right steps prefix true and "
                        + "skip the left child's whole leaf list. Hence the equality criterion "
                        + "retains occurrence identity even for identical subtrees at different addresses.")),
                    Paragraph(Text("Loday's original coordinate construction and proper-block "
                        + "Proposition 2.6 use n=m-1, r=a-1, d=b-a, x(i)=A(i), and "
                        + "S(d)=choose(b-a+1,2). Lemma 2.5 gives the full-tree total. "
                        + "Singleton and one-leaf cases have zero gaps and correspond to actual leaves."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("ancestor-area-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula LeOf(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula ResultFormula()
    {
        Formula t=V("t"), a=V("a"), b=V("b"), n=Seq(Mathbb, Grp(V("N")));
        Formula k=Seq(b, Sp, Minus, Sp, a, Sp, Plus, Sp, D(1));
        Formula c=Call("choose", k, D(2)), sum=Call("area", t, a, b);
        Formula result=And(LeOf(c, sum),
            IffOf(EqOf(sum, c), Call("CompleteSubtree", t, a, b)));
        Formula valid=Imp(LeOf(D(1), a),
            Imp(LeOf(a, b), Imp(LeOf(b, Call("length", t)), result)));
        return Disp(All("t", Seq(Operatorname, Grp(V("Source"))), All("a", n, All("b", n, valid))));

    }
}
