using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class GeometryEntranceRatioDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Entire same-word geometry fibers include every ordered shape and every pure substitution entrance.",
        H("Sharp Entrance Ratios on Entire Actual Geometry Fibers"),
        Blocks(
            Paragraph(Text("T is FreeMagma Bool. True is alpha and false is beta. Pairing retains both "
                + "children in order. The substitution rho sends alpha to beta, beta to (beta,alpha), "
                + "and a pair to the pair of substituted children. The word wd(t) lists every leaf of t "
                + "from left to right. G is the five-coordinate endpoint, signed area and two centered "
                + "moments of that same word, with unit steps (1,0) and (0,1). Its codomain Five is "
                + "the original real coordinate structure; no separate coordinate representatives are chosen.")),
            Def("WordFiber", "Whole word fiber", "WordFiber(g) is the subtype of all nonempty Boolean lists w with G(w)=g."),
            Def("TreeFiber", "Whole ordered tree fiber", "TreeFiber(g) is the subtype of all actual trees t:T with G(wd(t))=g. Every ordered shape is included."),
            Def("EntranceFiber", "All pure entrances", "EntranceFiber(g) consists of all triples (y,x,k):T times T times Nat with G(wd(y))=g and rho^k(x)=y. All natural k are permitted."),
            Def("N", "Actual leaf number", "N(g) is the natural floor of g.u+g.v. On any nonempty actual fiber it equals the positive word and tree length."),
            Def("L", "Forward geometry", "L(u,v,d,e,f)=(v,u+v,-d-v,v-f,-v-3d-e-f)."),
            Def("Linv", "Inverse candidate", "Linv(u,v,d,e,f)=(v-u,u,-d-u,u+3d+e-f,u-e). This is an inverse on the ambient coordinates; membership still requires an actual word or tree."),
            Def("letter", "Letter substitution", "letter(true)=[false], and letter(false)=[false,true]."),
            Def("sigma", "Actual word substitution", "sigma(w) is the concatenation of letter(c) for every letter occurrence c of w, in order."),
            Def("m", "Word cardinality", "m(g)=Nat.card(WordFiber(g)). The actual word carrier is proved finite before this definition."),
            Def("M", "Tree cardinality", "M(g)=Nat.card(TreeFiber(g)). The actual ordered tree carrier is proved finite before this definition."),
            Def("H", "Entrance cardinality", "H(g)=Nat.card(EntranceFiber(g)). Finiteness follows from a proved cutoff k<2N(g) for every legal entrance, together with finite current trees and finite possible source trees."),
            Def("pure", "Pure-word geometry", "pure(true,n)=(n,0,0,0,0), and pure(false,n)=(0,n,0,0,0). These are exactly the geometries of the corresponding repeated-letter words."),
            Def("B", "Sharp bound", "B(n) is three at n=2, five halves at n=3, and two otherwise. In particular B(1)=2 and B(n)=2 for n>=4."),
            Def("ba", "Two-leaf maximizer", "ba=(1,1,-1,1,-1) is the exact geometry of [false,true]."),
            Def("bab", "Three-leaf maximizer", "bab=(1,2,0,2,2) is the exact geometry of [false,true,false]."),
            Def("prefixMoment", "Prefix odd moment", "prefixMoment([])=0 and prefixMoment(a::l)=a+prefixMoment(l)+2 sum(l). For the reverse of the original descending rows, it is the sum of (2j-1)x(j) over the same word's ascending prefix counts."),
            Def("SourceGuards", "Same-word arithmetic guards", "SourceGuards(g) asserts one actual nonempty word w in WordFiber(g) and natural numbers k,q,t. They are, respectively, the sum of its original rows, the sum of the squared rows, and prefixMoment of the reverse rows. It includes k<=count(true,w) count(false,w), N(g)>0, g.u=count(true,w), g.v=count(false,w), and simultaneous integer d,e,f representing g.d,g.e,g.f. It also includes (g.d+g.u g.v)/2=k, (g.e+6g.u k-g.u^2 g.v)/6=q, and (g.f+6g.v k+g.u g.v^2)/6=t. Thus endpoints and all joint-moment guards belong to the same word, including pure words."),
            Def("upper", "Whole-fiber maximizer at every size", "upper(n)=ba at n=2, bab at n=3, and pure(false,n) otherwise."),
            Describe.Lean(DescribeId.Create("geometry-actual-fiber-counting"),
                DeclarationHandle.Create(Prefix + "actual_fiber_counting"),
                H("Actual Count Factorization and Recursion"),
                StatementSource.FromAuthor(CountingFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real candidate g, positive N gives the full ordered-shape "
                    + "factor Cat(N-1) times the whole word count. Independently of candidate validity, "
                    + "the all-entrance count splits into depth zero and the inverse candidate's all-entrance "
                    + "count. Applying sigma injects that inverse candidate's whole word fiber into the "
                    + "current one. Empty carriers contribute zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("geometry-uniform-entrance-estimate"),
                DeclarationHandle.Create(Prefix + "uniform_actual_entrance_estimate"),
                H("Uniform Bounds on Entire Actual Fibers"),
                StatementSource.FromAuthor(BoundFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The inequalities hold for all real candidates, hence for every "
                        + "nonempty actual geometry fiber. At one leaf the factor is two; at two leaves "
                        + "it is three; at three leaves the integer inequality 2H<=5M gives factor five "
                        + "halves; from four leaves onward the factor is two. The common factor three "
                        + "and the lower bound are included. These statements count all trees and all "
                        + "pure entrances; they impose no probability law on physical sources.")),
                    Paragraph(Text("The induction uses literal entrance recursion and injection of actual "
                        + "whole word fibers. A pure beta fiber has the same leaf count as its pure alpha "
                        + "inverse and has twice its tree count in entrances. Every other nonempty inverse "
                        + "has fewer leaves. The two distinct endpoint terms of the nonnegative Catalan "
                        + "recurrence show that adjacent positive indices at least double, leaving "
                        + "only the one-, two- and three-leaf inverse cases for direct arithmetic comparison."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("geometry-complete-sharp-source"),
                DeclarationHandle.Create(Prefix + "sharp_geometry_entrance_ratio"),
                H("Complete Sharp Ratios and Full-Fiber Attainment"),
                StatementSource.FromAuthor(CompleteFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every nonempty actual tree fiber supplies the same-word arithmetic guards, positive leaf and tree counts, the exact ratio bounds, and M<=H<=3M. No additional guard hypothesis is imposed on actual trees. The proof of the upper bound uses the entire inverse word fiber and every inverse tree entrance.")),
                    Paragraph(Text("At each positive n, the complete pure alpha and pure beta fibers each have one leaf word and Cat(n-1) ordered shapes. Their entrance ratios are one and two. The whole fiber at upper(n) attains B(n). At ba the unique word is beta alpha, with M=1 and H=3; at bab the unique word is beta alpha beta, with M=2 and H=5. The inverse chain bab, ba, beta, alpha counts all entrances by the proved recursion, including the primitive three-leaf shape. Consequently every uniform real upper bound on the ratios is at least three."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("geometry-fiber-" + (name switch
            { "m" => "wordcount", "M" => "treecount", "H" => "entrancecount", _ => name.ToLowerInvariant() })),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LeOf(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula LtOf(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula And(params Formula[] xs) => Seq(xs.Select((x, i) =>
        i == 0 ? Par(x) : Seq(Sp, Land, Sp, Par(x))).ToArray());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));

    private static Formula CountingFormula()
    {
        Formula g = V("g"), n = Call("N", g), m = Call("m", g), trees = Call("M", g);
        Formula entrances = Call("H", g), inverse = Call("Linv", g);
        return All("g", Call("Five"), And(
            Imp(LtOf(D(0), n), EqOf(trees, Mul(Call("Cat", Sub(n, D(1))), m))),
            EqOf(entrances, Add(trees, Call("H", inverse))),
            LeOf(Call("m", inverse), m), LeOf(trees, entrances)));
    }

    private static Formula BoundFormula()
    {
        Formula g = V("g"), n = Call("N", g), m = Call("M", g), h = Call("H", g);
        return All("g", Call("Five"), And(LeOf(m, h),
            Imp(EqOf(n, D(1)), LeOf(h, Mul(D(2), m))),
            Imp(EqOf(n, D(2)), LeOf(h, Mul(D(3), m))),
            Imp(EqOf(n, D(3)), LeOf(Mul(D(2), h), Mul(D(5), m))),
            Imp(LeOf(D(4), n), LeOf(h, Mul(D(2), m))), LeOf(h, Mul(D(3), m))));
    }
    private static Formula Ratio(Formula g) => new Formula.Fraction(Call("H", g), Call("M", g));
    private static Formula Nonempty(Formula g) => Call("Nonempty", Call("TreeFiber", g));
    private static Formula Word(params Formula[] letters) =>
        Seq(OpenBracket, Seq(letters.Select((x, i) => i == 0 ? x : Seq(Comma, Sp, x)).ToArray()), CloseBracket);
    private static Formula CompleteFormula()
    {
        Formula g = V("g"), n = V("n"), c = V("c"), w = V("w");
        Formula pt = Call("pure", V("true"), n), pf = Call("pure", V("false"), n);
        Formula up = Call("upper", n), ba = Call("ba"), bab = Call("bab");
        Formula universal = All("g", Call("Five"), Imp(Nonempty(g), And(
            Call("SourceGuards", g), LtOf(D(0), Call("N", g)), LtOf(D(0), Call("M", g)),
            LeOf(D(1), Ratio(g)), LeOf(Ratio(g), Call("B", Call("N", g))),
            LeOf(Call("M", g), Call("H", g)), LeOf(Call("H", g), Mul(D(3), Call("M", g))))));
        Formula attainment = All("n", Seq(Mathbb, Grp(V("N"))), Imp(LtOf(D(0), n), And(
            Nonempty(pt), Nonempty(pf), EqOf(Call("N", pt), n), EqOf(Call("N", pf), n),
            EqOf(Call("m", pt), D(1)), EqOf(Call("m", pf), D(1)),
            EqOf(Call("M", pt), Call("Cat", Sub(n, D(1)))), EqOf(Call("H", pt), Call("M", pt)),
            EqOf(Call("M", pf), Call("Cat", Sub(n, D(1)))), EqOf(Call("H", pf), Mul(D(2), Call("M", pf))),
            EqOf(Ratio(pt), D(1)), EqOf(Ratio(pf), D(2)),
            Nonempty(up), EqOf(Call("N", up), n), EqOf(Ratio(up), Call("B", n)))));
        Formula exceptions = And(Nonempty(ba), EqOf(Call("N", ba), D(2)),
            All("w", Call("WordFiber", ba), EqOf(Call("val", w), Word(V("false"), V("true")))),
            EqOf(Call("m", ba), D(1)), EqOf(Call("M", ba), D(1)), EqOf(Call("H", ba), D(3)),
            Nonempty(bab), EqOf(Call("N", bab), D(3)),
            All("w", Call("WordFiber", bab), EqOf(Call("val", w), Word(V("false"), V("true"), V("false")))),
            EqOf(Call("m", bab), D(1)), EqOf(Call("M", bab), D(2)), EqOf(Call("H", bab), D(5)));
        Formula sharp = All("c", Seq(Mathbb, Grp(V("R"))),
            Imp(All("g", Call("Five"), Imp(Nonempty(g), LeOf(Ratio(g), c))), LeOf(D(3), c)));
        return And(universal, attainment, exceptions, sharp);
    }

}
