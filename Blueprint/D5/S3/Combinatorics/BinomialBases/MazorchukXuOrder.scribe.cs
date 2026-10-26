using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases.MazorchukXuNotation;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases;

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
            Node("Order","Incident","Unordered incidence",All("A",Type,All("E",Rel(V("A")),Many("a b",V("A"),
                Iff(Call("Incident",V("E"),V("a"),V("b")),Or(Call("E",V("a"),V("b")),Call("E",V("b"),V("a"))))))),
                "The predicate asks for an edge in either order. The strict-order axiom prevents loops when E satisfies Rules.",DescribeRole.Definition),
            Node("Order","incident_ordinary_mono","Exceptional incidence increases with ordinary rank",IncidenceTheorem(),
                "An ordinary positive vertex has an edge from zero. For an exceptional vertex s, propagation handles the placements g<k<s and g<s<k; the maximum rule handles s<g<k. Hence incidence with ordinary vertices is a final segment.",DescribeRole.Theorem),
            Node("Order","exists_unique_ordinary_cutoff","The unique cutoff, including no ordinary vertices",Cutoff(),
                "The increasing list g contains M positive ordinary vertices and is indexed from zero. The unique cutoff c lies from zero through M; incidence holds exactly at indices at least c. Thus c=0 means full incidence and c=M means empty incidence. For M=0 the unique cutoff is zero.",DescribeRole.Theorem),
            Node("Order","thresholdEdges","Symmetric threshold edges",Ordered("A",Many("x y",Map(V("A"),Q),Many("a b",V("A"),
                Iff(Call("thresholdEdges",V("x"),V("y"),V("a"),V("b")),And(Lt(V("a"),V("b")),Lt(Call("y",V("a")),Call("x",V("b"))),Lt(Call("y",V("b")),Call("x",V("a")))))))),
                "Horizontal coordinates x respect the vertex order; the vertical thresholds y need not be monotone.",DescribeRole.Definition),
            Node("Order","rules_thresholdEdges","Threshold graphs satisfy both closure rules",Ordered("A",Many("x y",Map(V("A"),Q),
                Imp(Call("Monotone",V("x")),Call("Rules",Call("thresholdEdges",V("x"),V("y"))))))),
                "For P the two cross inequalities follow by horizontal monotonicity. For J, the premise beginning at the larger lower endpoint gives one inequality and the premise ending at the larger upper endpoint gives the other. Only monotonicity, rather than strict monotonicity, of x is required.",DescribeRole.Theorem),
            Node("Order","adjoinGreatest","A greatest universal vertex",Ordered("A",All("E",Rel(V("A")),Many("t a b",V("A"),
                Iff(Call("adjoinGreatest",V("E"),V("t"),V("a"),V("b")),And(Lt(V("a"),V("b")),Le(V("b"),V("t")),Or(Eq(V("b"),V("t")),Call("E",V("a"),V("b")))))))),
                "Keep old edges below t and connect t to every smaller vertex.",DescribeRole.Definition),
            Node("Order","rules_adjoinGreatest_iff","Adjoining and deleting a universal greatest vertex",Universal(),
                "If all old edges have strictly increasing endpoints below t, adjoining t is equivalent to the old closure rules. A forced edge ending at t is present by universality; every other instance uses the old rules. Repeated application permits a finite universal tail.",DescribeRole.Theorem)), []));

    private static Formula LiftTheorem(bool converse)
    {
        var A=V("A");var B=V("B");var E=V("E");var f=V("f");var s=V("s");
        var lift=Call("cliqueLift",E,f);
        Formula body=Imp(And(Call("Rules",E),Call("Monotone",f)),Call("Rules",lift));
        if(converse)
            body=All("s",Map(A,B),Imp(And(Many("a b",A,Imp(Call("E",V("a"),V("b")),Lt(V("a"),V("b")))),
                Call("Monotone",f),Call("StrictMono",s),All("a",A,Eq(Call("f",Call("s",V("a"))),V("a")))),
                Iff(Call("Rules",lift),Call("Rules",E))));
        return Ordered("A",Ordered("B",All("E",Rel(A),All("f",Map(B,A),body))));
    }
    private static Formula CliqueLift() => All("A",Type,Ordered("B",All("E",Rel(V("A")),All("f",Map(V("B"),V("A")),Many("a b",V("B"),
        Iff(Call("cliqueLift",V("E"),V("f"),V("a"),V("b")),And(Lt(V("a"),V("b")),Or(Eq(Call("f",V("a")),Call("f",V("b"))),Call("E",Call("f",V("a")),Call("f",V("b"))))))))));
    private static Formula IncidenceTheorem() => All("E",Rel(N),Many("s g k",N,
        Imp(And(Call("Rules",V("E")),Not(Call("E",D(0),V("s"))),Call("E",D(0),V("g")),Call("E",D(0),V("k")),Lt(V("g"),V("k")),Call("Incident",V("E"),V("s"),V("g"))),
            Call("Incident",V("E"),V("s"),V("k")))));
    private static Formula Cutoff()
    {
        var E=V("E");var s=V("s");var M=V("M");var g=V("g");var r=V("r");
        Formula Property(Formula c)=>And(Le(c,M),All("r",Call("Fin",M),Iff(Call("Incident",E,s,Call("g",r)),Le(c,Call("val",r)))));
        return All("E",Rel(N),Many("s M",N,All("g",Map(Call("Fin",M),N),
            Imp(And(Call("Rules",E),Not(Call("E",D(0),s)),Call("StrictMono",g),All("r",Call("Fin",M),Call("E",D(0),Call("g",r)))),
                Ex("c",N,And(Property(V("c")),All("d",N,Imp(Property(V("d")),Eq(V("d"),V("c"))))))))));
    }
    private static Formula Universal() => Ordered("A",All("E",Rel(V("A")),All("t",V("A"),
        Imp(Many("a b",V("A"),Imp(Call("E",V("a"),V("b")),And(Lt(V("a"),V("b")),Lt(V("b"),V("t"))))),
            Iff(Call("Rules",Call("adjoinGreatest",V("E"),V("t"))),Call("Rules",V("E")))))));
}
