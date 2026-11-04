using System.Linq;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases.MazorchukXuPatternsNotation;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases;

internal static class MazorchukXuPatternsNotation
{
    internal static Formula N => Fn("Nat");
    internal static Formula Q => Fn("Rat");
    internal static Formula Prop => Fn("Prop");
    internal static Formula Ty => Fn("Type");
    internal static Formula Pairs => Fn("Prod", N, N);
    internal static Formula Points => Fn("Finset", Pairs);
    internal static Formula V(string name) => F.Id(name);
    internal static Formula Fn(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    internal static Formula Apply(Formula fn, params Formula[] args) =>
        Seq(fn, Open, new Formula.LatexSequence([.. args.SelectMany((a, i) =>
            i == 0 ? new[] { a } : new[] { Comma, Sp, a })]), Close);
    internal static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    internal static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    internal static Formula Many(string names, Formula domain, Formula body)
    {
        foreach (var name in names.Split(' ').Reverse()) body = All(name, domain, body);
        return body;
    }
    internal static Formula Par(Formula a) => Seq(Open, a, Close);
    internal static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Par(a), op, Par(b));
    internal static Formula And(params Formula[] xs) =>
        xs.Aggregate((a, b) => Logic(a, FormulaLogicOperator.And, b));
    internal static Formula Or(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Or, b);
    internal static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    internal static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    internal static Formula Not(Formula a) => Seq(Neg, Sp, Par(a));
    internal static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    internal static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    internal static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    internal static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    internal static Formula Subset(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.SubsetOf, b);
    internal static Formula Plus(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    internal static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    internal static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    internal static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);
    internal static Formula Set(string name, Formula domain, Formula predicate) =>
        Seq(OpenBrace, V(name), Sp, InMacro, Sp, domain, Bar, Sp, predicate, CloseBrace);
    internal static Formula Rel(Formula a) => new Formula.TypeArrow(a, new Formula.TypeArrow(a, Prop));
    internal static Formula Map(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    internal static Formula Ordered(string name, Formula body) =>
        All(name, Ty, Seq(OpenBracket, Fn("LinearOrder", V(name)), CloseBracket, Sp, body));
    internal static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/mazorchukxu2026cokernel");
    internal static DocumentBlock Node(string module, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature = false) =>
        Describe.Lean(DescribeId.Create("mazorchuk-xu-" + module.ToLowerInvariant() + "-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/Combinatorics/BinomialBases/MazorchukXu" + module + "." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}


internal sealed class MazorchukXuPatternsDocument : IScribeDocumentDefinition
{
    private static Formula I => V("i");
    private static Formula FinI => Fn("Fin", I);
    private static Formula List => Map(FinI, N);
    private static Formula P => V("p");
    private static Formula C => V("c");
    private static Formula B => V("B");
    private static Formula Vert => Fn("CoordinateVertex", P);
    private static Formula Edge(Formula p, Formula c) => Fn("coordinateEdges", p, c, B);
    private static Formula Edges => Edge(P, C);
    private static Formula FVert => Fn("BoundedCoordinateVertex", V("M"), P);
    private static Formula Bounded => Fn("boundedCoordinateEdges", V("M"), P, C, B);
    private static Formula Params(Formula body) => All("i", N, Many("p c", List, All("B", Rel(FinI), body)));
    private static Formula At(Formula f, string x) => Apply(f, V(x));
    private static Formula Compose(string f, Formula g) => Fn("comp", V(f), g);
    private static Formula Bound(Formula f) => All("j", FinI, Le(Apply(f, V("j")), V("M")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coordinate graphs keep zero, repeated positions and cutoffs, arbitrary exceptional edges, and an ordinary clique. Their admissibility is unchanged by increasing coordinate refinements or by a universal ordinary tail.",
        H("Weak coordinate patterns and literal graph realization"),
        Blocks(
            Node("Patterns", "CoordinateVertex", "Ordinary ranks and labelled exceptions",
                All("i", N, All("p", List, Fn("Equiv", Vert, Fn("Sum", N, FinI)))),
                "The two constructors are ordinary(r) for every natural rank r, including the anchor zero, and exceptional(j) for j in Fin i. The position list is a type parameter, so each graph has its own order. The displayed equivalence describes the two constructors; it does not identify their order with a sum order.", DescribeRole.Definition),
            Node("Patterns", "coordinateKey", "Lexicographic vertex keys",
                All("i", N, All("p", List, And(
                    All("r", N, Eq(Fn("coordinateKey", P, Fn("ordinary", V("r"))), Pair(V("r"), Fn("zero")))),
                    All("j", FinI, Eq(Fn("coordinateKey", P, Fn("exceptional", V("j"))),
                        Pair(At(P, "j"), Plus(Fn("val", V("j")), Fn("one")))))))),
                "Keys are ordered lexicographically. Ordinary r precedes every exception in position r, and the exceptional index breaks position ties. Distinct vertices have distinct keys. The coordinate linear order is pulled back along this injection.", DescribeRole.Definition),
            Node("Patterns", "coordinateEdges", "Edges with every tie and exceptional bit retained", EdgeFormula(),
                "Only increasing endpoint pairs are edges. All ordinary pairs are adjacent. The pair involving exceptional j and ordinary rank r is adjacent exactly when c(j)<r, in either possible endpoint order. The ordered exceptional pair j,k is adjacent exactly when B(j,k). No condition on B, positivity, distinctness or monotonicity of p or c is built into this definition.", DescribeRole.Definition),
            Node("Patterns", "coordinate_rules_refinement_iff", "Increasing refinements preserve all weak patterns", Refinement(),
                "For an increasing map e, send ordinary rank r to the least k with r<=e(k), and leave each exceptional label fixed. This collapse is monotone. Its increasing section sends ordinary k to e(k), again fixing exceptional labels. Incidence transforms because e(c)<r is equivalent to c<ceil_e(r). Hence the expanded graph is exactly the clique lift of the original graph, including all collapsed ordinary fibers and every equality between coordinate entries. The clique-lift equivalence proves both directions of Rules. The hypothesis e(0)=0 retains the distinguished zero used for source patterns.", DescribeRole.Theorem),
            Node("Patterns", "universalTail", "A universal tail above an initial segment",
                Ordered("A", All("E", Rel(V("A")), All("S", Map(V("A"), Prop), Many("a b", V("A"),
                    Iff(Fn("universalTail", V("E"), V("S"), V("a"), V("b")),
                        And(Lt(V("a"), V("b")), Or(Not(At(V("S"), "b")), Fn("E", V("a"), V("b"))))))))),
                "Every increasing pair ending outside S is added; edges within S are read from E. When S is downward closed and E is supported there, this operation preserves and reflects both ordered closure rules, even for an infinite tail.", DescribeRole.Definition),
            Node("Patterns", "coordinateInside", "The finite coordinate segment",
                All("i", N, All("p", List, All("M", N, And(
                    All("r", N, Iff(Fn("coordinateInside", V("M"), Fn("ordinary", V("r"))), Le(V("r"), V("M")))),
                    All("j", FinI, Fn("coordinateInside", V("M"), Fn("exceptional", V("j")))))))),
                "The segment contains ordinary ranks zero through M and every exceptional vertex. Under p(j)<=M it is an initial segment in the coordinate order.", DescribeRole.Definition),
            Node("Patterns", "boundedCoordinateEdges", "Edges on the finite coordinate segment",
                Params(All("M", N, Many("u v", Vert, Iff(Fn("boundedCoordinateEdges", V("M"), P, C, B, V("u"), V("v")),
                    And(Apply(Edges, V("u"), V("v")), Fn("coordinateInside", V("M"), V("v"))))))),
                "Retain coordinate edges whose upper endpoint belongs to the finite segment. When positions are bounded by M the lower endpoint belongs to the segment as well.", DescribeRole.Definition),
            Node("Patterns", "coordinateInside_downward", "Coordinate segments are initial segments", Downward(),
                "If every exceptional position is at most M, every vertex preceding a vertex in the segment is also in the segment. An ordinary vertex before exception j has rank at most p(j); all exceptions belong to the segment.", DescribeRole.Theorem),
            Node("Patterns", "coordinate_rules_bounded_iff", "Deleting every universal ordinary tail", BoundedRules(),
                "When positions and cutoffs are at most M, each ordinary vertex of rank greater than M follows every exception and is adjacent to every earlier vertex. The infinite graph is exactly the universal-tail extension of the bounded graph. The universal-tail argument gives equivalence, including M=0 and tied or zero entries.", DescribeRole.Theorem),
            Node("Patterns", "BoundedCoordinateVertex", "The finite vertex subtype",
                All("i", N, All("M", N, All("p", List,
                    Eq(FVert, Set("u", Vert, Fn("coordinateInside", V("M"), V("u"))))))),
                "This subtype inherits the coordinate order. It includes the anchor even when there are no positive ordinary vertices.", DescribeRole.Definition),
            Node("Patterns", "coordinateLabel", "Canonical natural labels", LabelFormula(),
                "An ordinary vertex of rank r has r earlier ordinary vertices and one earlier exceptional vertex for each p(j)<r. Exception j has p(j) earlier positive ordinary vertices, the anchor, and j earlier exceptions. These formulas include every zero and tied position.", DescribeRole.Definition),
            Node("Patterns", "coordinateLabel_strictMono", "Labels preserve the coordinate order",
                All("i",N,All("p",List,Imp(Fn("Monotone",P),Fn("StrictMono",Fn("coordinateLabel",P))))),
                "For an increasing position list, the number of positions below r is a nondecreasing function of r. Its value is at most j when r<=p(j), and exceeds j when p(j)<r. These inequalities prove the two mixed vertex comparisons; ordinary and exceptional comparisons follow from the rank and index increments.", DescribeRole.Theorem),
            Node("Patterns", "coordinateLabel_bound", "Labels stay in the full finite interval", LabelBound(),
                "There are i exceptional positions in total. Ordinary rank r<=M therefore has label at most M+i. The j-th exception has p(j)<=M and j<i, giving the same bound. Monotonicity is not needed for this bound.", DescribeRole.Theorem),
            Node("Patterns", "coordinateLabel_bijective", "Every finite label occurs exactly once", LabelBijection(),
                "The finite vertex set has M+1 ordinary vertices and i exceptions. The strict label map injects it into the M+i+1 labels zero through M+i, so equal finite cardinalities give bijectivity. This includes the single anchor when M=i=0. The theorem states bijectivity of the map into Fin(M+i+1); the display gives its equivalent uniqueness and full natural-interval surjectivity clauses.", DescribeRole.Theorem),
            Node("Patterns", "edgeFamily_coordinate_realization", "An exact increasing realization of every source graph", Realization(),
                "Extract the ordinary and exceptional lists from the literal edge family. Ordinary rank zero maps to the anchor; positive ordinary rank r maps to entry r-1 of the ordered ordinary list; exceptional j maps to the j-th missing anchor neighbor. Position and cutoff laws give the mixed edges, the ordinary vertices form a clique, and B retains each actual exceptional edge. The map is increasing and bijects onto every natural vertex from zero through n+1. Thus this is an exact edge correspondence, including zero positions, coinciding coordinates and an empty positive ordinary list. It does not count coordinate patterns or assert polynomiality.", DescribeRole.Theorem)), []));

    private static Formula EdgeFormula()
    {
        var O = Fn("ordinary", V("r")); var T = Fn("ordinary", V("s"));
        var J = Fn("exceptional", V("j")); var K = Fn("exceptional", V("k"));
        return Params(And(
            Many("r s", N, Iff(Apply(Edges,O,T),Lt(V("r"),V("s")))),
            All("r",N,All("j",FinI,Iff(Apply(Edges,O,J),And(Le(V("r"),At(P,"j")),Lt(At(C,"j"),V("r")))))),
            All("r",N,All("j",FinI,Iff(Apply(Edges,J,O),And(Lt(At(P,"j"),V("r")),Lt(At(C,"j"),V("r")))))),
            Many("j k",FinI,Iff(Apply(Edges,J,K),And(Lt(J,K),Fn("B",V("j"),V("k")))))));
    }
    private static Formula Refinement() => Params(All("e",Map(N,N),
        Imp(And(Fn("StrictMono",V("e")),Eq(Fn("e",Fn("zero")),Fn("zero"))),
            Iff(Fn("Rules",Edge(Compose("e",P),Compose("e",C))),Fn("Rules",Edges)))));
    private static Formula BoundedRules() => Params(All("M",N,
        Imp(And(Bound(P),Bound(C)),Iff(Fn("Rules",Bounded),Fn("Rules",Edges)))));
    private static Formula Realization()
    {
        var n=V("n");var m=Sub(Plus(n,Fn("one")),I);var a=V("A");
        var fv=Fn("BoundedCoordinateVertex",m,P);var f=V("f");
        var conclusion=And(Fn("Monotone",P),All("j",FinI,Le(At(P,"j"),m)),
            All("j",FinI,Le(At(C,"j"),m)),Many("j k",FinI,Imp(Fn("B",V("j"),V("k")),Lt(V("j"),V("k")))),Fn("StrictMono",f),
            All("u",fv,Le(At(f,"u"),Plus(n,Fn("one")))),
            All("a",N,Imp(Le(V("a"),Plus(n,Fn("one"))),Ex("u",fv,Eq(At(f,"u"),V("a"))))),
            Many("u v",fv,Iff(Mem(Pair(At(f,"u"),At(f,"v")),a),
                Apply(Edges,Fn("val",V("u")),Fn("val",V("v"))))));
        return Many("n i",N,Imp(Le(I,Plus(n,Fn("one"))),All("A",Points,
            Imp(Mem(a,Fn("edgeFamily",n,m)),Ex("p",List,Ex("c",List,Ex("B",Rel(FinI),Ex("f",Map(fv,N),conclusion))))))));
    }
    private static Formula Downward() => All("i",N,All("M",N,All("p",List,
        Imp(Bound(P),Many("u v",Vert,Imp(And(Le(V("u"),V("v")),Fn("coordinateInside",V("M"),V("v"))),
            Fn("coordinateInside",V("M"),V("u"))))))));
    private static Formula LabelFormula() => All("i",N,All("p",List,And(
        All("r",N,Eq(Fn("coordinateLabel",P,Fn("ordinary",V("r"))),
            Plus(V("r"),Fn("card",Set("j",FinI,Lt(At(P,"j"),V("r"))))))),
        All("j",FinI,Eq(Fn("coordinateLabel",P,Fn("exceptional",V("j"))),
            Plus(Plus(At(P,"j"),Fn("val",V("j"))),Fn("one")))))));
    private static Formula LabelBound() => All("i",N,All("M",N,All("p",List,
        Imp(Bound(P),All("u",FVert,Le(Fn("coordinateLabel",P,Fn("val",V("u"))),Plus(V("M"),I)))))));
    private static Formula LabelBijection()
    {
        Formula Label(string u) => Fn("coordinateLabel",P,Fn("val",V(u)));
        return All("i",N,All("M",N,All("p",List,Imp(And(Fn("Monotone",P),Bound(P)),And(
            Many("u v",FVert,Imp(Eq(Label("u"),Label("v")),Eq(V("u"),V("v")))),
            All("a",N,Imp(Le(V("a"),Plus(V("M"),I)),Ex("u",FVert,Eq(Label("u"),V("a"))))))))));
    }

}
