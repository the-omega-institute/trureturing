using F = StrataLint.Scribe.FormulaDsl;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases.MazorchukXuOrderNotation;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases;

internal static class MazorchukXuOrderNotation
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

internal sealed class MazorchukXuOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered clique fibers, exceptional incidence cutoffs and monotone threshold edges supply structural ingredients for finite order-pattern counting.",
        H("Expansion and cutoff structure of ordered closure"),
        Blocks(
            Node("Order","cliqueLift","Clique-fiber expansion",CliqueLift(),
                "The map f collapses consecutive ordered fibers. Each fiber becomes a clique; between different fibers adjacency is read from E. No surjectivity, finiteness or two-element-fiber hypothesis is needed for forward preservation.",DescribeRole.Definition),
            Node("Order","rules_cliqueLift","Preservation under monotone expansion",LiftTheorem(false),
                "For P, a collapsed middle endpoint uses the selected upper edge, and a collapsed upper pair uses its fiber clique. For J, either the original J applies below the collapsed middle fiber, or a premise ending at the largest upper endpoint and P supply the required edge. These cases include every repetition and every collapsed inequality.",DescribeRole.Theorem),
            Node("Order","rules_cliqueLift_iff","Two-way compression with an increasing section",LiftTheorem(true),
                "Forward expansion is complemented by restriction along an increasing section s of f. This establishes both directions of admissibility for the clique-fiber construction. It does not by itself identify the position/cutoff fibers of an arbitrary source graph or count their patterns.",DescribeRole.Theorem),
            Node("Order","Incident","Unordered incidence",All("A",Ty,All("E",Rel(V("A")),Many("a b",V("A"),
                Iff(Fn("Incident",V("E"),V("a"),V("b")),Or(Fn("E",V("a"),V("b")),Fn("E",V("b"),V("a"))))))),
                "The predicate asks for an edge in either order. The strict-order axiom prevents loops when E satisfies Rules.",DescribeRole.Definition),
            Node("Order","incident_ordinary_mono","Exceptional incidence increases with ordinary rank",IncidenceTheorem(),
                "An ordinary positive vertex has an edge from zero. For an exceptional vertex s, propagation handles the placements g<k<s and g<s<k; the maximum rule handles s<g<k. Hence incidence with ordinary vertices is a final segment.",DescribeRole.Theorem),
            Node("Order","exists_unique_ordinary_cutoff","The unique cutoff, including no ordinary vertices",Cutoff(),
                "The increasing list g contains M positive ordinary vertices and is indexed from zero. The unique cutoff c lies from zero through M; incidence holds exactly at indices at least c. Thus c=0 means full incidence and c=M means empty incidence. For M=0 the unique cutoff is zero.",DescribeRole.Theorem),
            Node("Order","thresholdEdges","Symmetric threshold edges",Ordered("A",Many("x y",Map(V("A"),Q),Many("a b",V("A"),
                Iff(Fn("thresholdEdges",V("x"),V("y"),V("a"),V("b")),And(Lt(V("a"),V("b")),Lt(Fn("y",V("a")),Fn("x",V("b"))),Lt(Fn("y",V("b")),Fn("x",V("a")))))))),
                "Horizontal coordinates x respect the vertex order; the vertical thresholds y need not be monotone.",DescribeRole.Definition),
            Node("Order","rules_thresholdEdges","Threshold graphs satisfy both closure rules",Ordered("A",Many("x y",Map(V("A"),Q),
                Imp(Fn("Monotone",V("x")),Fn("Rules",Fn("thresholdEdges",V("x"),V("y")))))),
                "For P the two cross inequalities follow by horizontal monotonicity. For J, the premise beginning at the larger lower endpoint gives one inequality and the premise ending at the larger upper endpoint gives the other. Only monotonicity, rather than strict monotonicity, of x is required.",DescribeRole.Theorem),
            Node("Order","adjoinGreatest","A greatest universal vertex",Ordered("A",All("E",Rel(V("A")),Many("t a b",V("A"),
                Iff(Fn("adjoinGreatest",V("E"),V("t"),V("a"),V("b")),And(Lt(V("a"),V("b")),Le(V("b"),V("t")),Or(Eq(V("b"),V("t")),Fn("E",V("a"),V("b")))))))),
                "Keep old edges below t and connect t to every smaller vertex.",DescribeRole.Definition),
            Node("Order","rules_adjoinGreatest_iff","Adjoining and deleting a universal greatest vertex",Universal(),
                "If all old edges have strictly increasing endpoints below t, adjoining t is equivalent to the old closure rules. A forced edge ending at t is present by universality; every other instance uses the old rules. Repeated application permits a finite universal tail.",DescribeRole.Theorem)), []));

    private static Formula LiftTheorem(bool converse)
    {
        var A=V("A");var B=V("B");var E=V("E");var f=V("f");var s=V("s");
        var lift=Fn("cliqueLift",E,f);
        Formula body=Imp(And(Fn("Rules",E),Fn("Monotone",f)),Fn("Rules",lift));
        if(converse)
            body=All("s",Map(A,B),Imp(And(Many("a b",A,Imp(Fn("E",V("a"),V("b")),Lt(V("a"),V("b")))),
                Fn("Monotone",f),Fn("StrictMono",s),All("a",A,Eq(Fn("f",Fn("s",V("a"))),V("a")))),
                Iff(Fn("Rules",lift),Fn("Rules",E))));
        return Ordered("A",Ordered("B",All("E",Rel(A),All("f",Map(B,A),body))));
    }
    private static Formula CliqueLift() => All("A",Ty,Ordered("B",All("E",Rel(V("A")),All("f",Map(V("B"),V("A")),Many("a b",V("B"),
        Iff(Fn("cliqueLift",V("E"),V("f"),V("a"),V("b")),And(Lt(V("a"),V("b")),Or(Eq(Fn("f",V("a")),Fn("f",V("b"))),Fn("E",Fn("f",V("a")),Fn("f",V("b")))))))))));
    private static Formula IncidenceTheorem() => All("E",Rel(N),Many("s g k",N,
        Imp(And(Fn("Rules",V("E")),Not(Fn("E",D(0),V("s"))),Fn("E",D(0),V("g")),Fn("E",D(0),V("k")),Lt(V("g"),V("k")),Fn("Incident",V("E"),V("s"),V("g"))),
            Fn("Incident",V("E"),V("s"),V("k")))));
    private static Formula Cutoff()
    {
        var E=V("E");var s=V("s");var M=V("M");var g=V("g");var r=V("r");
        Formula Property(Formula c)=>And(Le(c,M),All("r",Fn("Fin",M),Iff(Fn("Incident",E,s,Fn("g",r)),Le(c,Fn("val",r)))));
        return All("E",Rel(N),Many("s M",N,All("g",Map(Fn("Fin",M),N),
            Imp(And(Fn("Rules",E),Not(Fn("E",D(0),s)),Fn("StrictMono",g),All("r",Fn("Fin",M),Fn("E",D(0),Fn("g",r)))),
                Ex("c",N,And(Property(V("c")),All("d",N,Imp(Property(V("d")),Eq(V("d"),V("c"))))))))));
    }
    private static Formula Universal() => Ordered("A",All("E",Rel(V("A")),All("t",V("A"),
        Imp(Many("a b",V("A"),Imp(Fn("E",V("a"),V("b")),And(Lt(V("a"),V("b")),Lt(V("b"),V("t"))))),
            Iff(Fn("Rules",Fn("adjoinGreatest",V("E"),V("t"))),Fn("Rules",V("E")))))));
}
