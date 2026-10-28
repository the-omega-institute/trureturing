using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class AmoebaHostDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/AmoebaHost.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite layered supertree preserves every initial tree, realizes all arm paths simultaneously for every copy, and is confining under total-edge minimization.",
        H("Finite Buffered Hosts for Ordinary Amoebas"),
        Blocks(
            Paragraph(Text(
                "Host, extensionGraph and HasExtension have the meanings given in AmoebaConfinement. "
                + "The source target is Gurvich–Krnc–Vyalyi Conjecture 1, arXiv:2401.07484v1/v2 and DOI 10.1007/s00025-025-02421-6. "
                + "The construction supplies a finite host for every initial finite tree and controls all copies and all multiplicity placements. "
                + "All nonnegative extension lengths and multiplicities are retained. The final assertion uses the finite source convention; "
                + "it makes no claim about infinite hosts with cardinal edge minimization.")),
            Paragraph(Text(
                "sprout(P,p) has vertex type V disjoint union L. It retains P on V and makes each a in L a new leaf adjacent only to p(a). "
                + "A Layered(T,M,q,N) consists of a finite tree S, a core copy of T, and a natural-valued level function. "
                + "The level is zero exactly on the core and at most N everywhere. Core degrees are at least M, "
                + "positive levels below N have degree q, and level N has degree one. Adjacent levels differ by at most one. "
                + "The construction starts with M new leaves at each core vertex, then repeatedly attaches q−1 new leaves to every outer leaf. "
                + "Counting old edges and new leaves proves that each stage is still a finite tree.")),
            Node("copy_level_bound", "Every copy remains close to the core", CopyLevelFormula(),
                "Choose a maximum-degree vertex in H. Its image cannot lie outside the core because every outside degree is at most q. "
                + "For each other vertex, the unique H-path from that vertex maps to an actual host path. Its length is less than the order of H. "
                + "The level changes by at most one per edge, so the stated bound holds for every vertex of every copy."),
            Node("exists_buffered_host", "All-copy degree budgets in one finite supertree", BufferFormula(),
                "Put k equal to the sum of m. Select q between 2 and k+2 avoiding every interval from degree(v) to degree(v)+m(v). "
                + "Use core degree budget M equal to maximum degree plus k plus two, and outer depth equal to the order of H plus l plus one. "
                + "Every copy lies below the order of H in level. At a core vertex the M budget supplies its degree demand. "
                + "At a branch vertex its degree is q; containment gives degree(v) at most q, and the safe-degree choice then supplies degree(v)+m(v). "
                + "Every vertex below the outer level has degree at least two. The core copy explicitly preserves the arbitrary initial T; "
                + "no assumption that an extension is already present is used."),
            Node("sprout_copy", "Jointly fresh leaf attachment", SproutFormula(),
                "The image of a connected tree inside a tree is induced: its paths are unique, so an extra image edge would form a cycle. "
                + "A vertex outside that image cannot be adjacent to two distinct image vertices for the same reason. "
                + "At each parent, removing its image neighbors leaves enough neighbors for the prescribed new leaves. "
                + "Choose an injection on each parent fiber. Distinct fibers cannot collide by the unique-attachment property, "
                + "so all chosen leaves are fresh and jointly distinct."),
            Node("hasExtension_one", "The simultaneous first arm edges", OneFormula(),
                "Apply the joint leaf-attachment theorem to the root-occurrence type consisting of pairs (v,a) with a below m(v). "
                + "Its parent fiber over v has exactly m(v) elements. Forgetting the unique Fin(1) coordinate identifies these leaves "
                + "with the explicit length-one extension graph. Thus every first arm edge is realized simultaneously. "
                + "These edges initialize the paths in the following continuation lemma."),
            Node("hasExtension_of_buffer", "Simultaneous arms of every finite length", ArmsFormula(),
                "For zero length the extension is the existing copy. For positive length, start with the jointly fresh first edges. "
                + "Continue each arm by choosing a neighbor other than its predecessor. The level buffer keeps every endpoint below the outer leaves. "
                + "Acyclicity makes every such continuation a path. A path whose first edge leaves the connected copy cannot return to it: "
                + "a return would give two distinct paths between copy vertices. Likewise, two off-copy arm tails can meet only if their "
                + "roots and first edges agree. The first-edge injection then identifies their root occurrences. Path simplicity identifies "
                + "their position indices. The resulting injective homomorphism realizes the entire explicit extension graph."),
            Node("total_confinement", "The full ordinary-amoeba total-confinement assertion", TotalFormula(),
                "For any finite tree H and nonnegative multiplicities, assume its maximum degree exceeds the multiplicity sum plus two. "
                + "Given an arbitrary finite initial T containing H, use its buffered layered host S. Every copy has the root degree budgets "
                + "and the full path-length margin, so the simultaneous extension lemma applies to every copy, with its own transported multiplicities. "
                + "The minimum-total-edge bridge makes every one of these copies dead for every minimizing growth. Composing the preserved core "
                + "embedding with the initial copy also proves that S admits a copy. Thus S is confining and contains the arbitrary T.")),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose) => Describe.Lean(
        DescribeId.Create("amoeba-host-" + name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] a) => a.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(s))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(s)), [.. a]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(Seq(Open, a, Close), op, Seq(Open, b, Close));
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Add(params Formula[] a) => Join(Plus, a);
    private static Formula Join(Formula op, Formula[] a) => a.Length == 2 ? Seq(a[0], Sp, op, Sp, a[1])
        : Seq(a[0], Sp, op, Sp, Join(op, a[1..]));
    private static Formula Nat => Call("Nat");
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Finite(string s, Formula b) => All(s, Call("Type"), Seq(OpenBracket, Call("Fintype", Id(s)), CloseBracket, Sp, b));
    private static Formula Graph(Formula x) => Call("graph", x);
    private static Formula Copy(Formula x, Formula y) => Call("Copy", x, y);
    private static Formula Level(Formula x) => Call("level", Id("A"), x);
    private static Formula Image(Formula x) => Call("c", x);
    private static Formula Order => Call("card", Id("V"));
    private static Formula Demand => Add(Call("degree", Id("H"), Id("v")), Call("m", Id("v")));
    private static Formula At(Formula g, Formula v) => Call("degree", g, v);
    private static Formula HostGraph => Graph(Call("host", Id("A")));

    private static Formula CopyLevelFormula()
    {
        var result = Ex("v", Id("V"), And(Eq(Level(Image(Id("v"))), D(0)),
            All("w", Id("V"), Lt(Level(Image(Id("w"))), Order))));
        var c = All("c", Copy(Id("H"), HostGraph), result);
        var hypotheses = Imp(Le(D(1), Id("q")), Imp(Lt(Id("q"), Call("maxDegree", Id("H"))), c));
        var a = All("A", Call("Layered", Id("T"), Id("M"), Id("q"), Id("N")), hypotheses);
        return Disp(Finite("V", All("H", Call("SimpleGraph", Id("V")), Imp(Call("IsTree", Id("H")),
            All("T", Call("Host"), All("M", Nat, All("q", Nat, All("N", Nat, a))))))));
    }
    private static Formula BufferFormula()
    {
        var copies = All("c", Copy(Id("H"), HostGraph), All("v", Id("V"), Lt(Level(Image(Id("v"))), Order)));
        var budgets = All("c", Copy(Id("H"), HostGraph), All("v", Id("V"), Le(Demand, At(HostGraph, Image(Id("v"))))));
        var depth = Add(Order, Id("l"), D(1));
        var interior = All("x", Call("Vertex", Call("host", Id("A"))),
            Imp(Lt(Level(Id("x")), depth), Le(D(2), At(HostGraph, Id("x")))));
        var bounds = And(Le(D(2), Id("q")), And(Le(Id("q"), Add(Call("sum", Id("m")), D(2))),
            And(Lt(Id("q"), Call("maxDegree", Id("H"))), And(Le(D(2), Id("M")), And(copies, And(budgets, interior))))));
        var result = Ex("q", Nat, Ex("M", Nat, Ex("A", Call("Layered", Id("T"), Id("M"), Id("q"), depth), bounds)));
        var hypothesis = Lt(Add(Call("sum", Id("m")), D(2)), Call("maxDegree", Id("H")));
        return Disp(Finite("V", All("H", Call("SimpleGraph", Id("V")), Imp(Call("IsTree", Id("H")),
            All("m", Fn(Id("V"), Nat), All("l", Nat, Imp(hypothesis, All("T", Call("Host"), result))))))));
    }
    private static Formula SproutFormula()
    {
        var fibers = Call("card", Call("parentFiber", Id("p"), Id("v")));
        var budget = All("v", Id("V"), Le(Add(At(Id("P"), Id("v")), fibers), At(Id("G"), Image(Id("v")))));
        var result = Ex("e", Copy(Call("sprout", Id("P"), Id("p")), Id("G")),
            All("v", Id("V"), Eq(Call("e", Call("inl", Id("v"))), Image(Id("v")))));
        var body = All("c", Copy(Id("P"), Id("G")), All("p", Fn(Id("L"), Id("V")), Imp(budget, result)));
        return Disp(Finite("V", Finite("W", Finite("L", All("P", Call("SimpleGraph", Id("V")),
            All("G", Call("SimpleGraph", Id("W")), Imp(Call("IsTree", Id("P")), Imp(Call("IsTree", Id("G")), body))))))));
    }
    private static Formula OneFormula()
    {
        var budget = All("v", Id("V"), Le(Demand, At(Graph(Id("G")), Image(Id("v")))));
        var result = Imp(budget, Call("HasExtension", Id("m"), D(1), Id("c")));
        return Disp(Finite("V", All("H", Call("SimpleGraph", Id("V")), Imp(Call("IsTree", Id("H")),
            All("m", Fn(Id("V"), Nat), All("G", Call("Host"), All("c", Copy(Id("H"), Graph(Id("G"))), result)))))));
    }
    private static Formula ArmsFormula()
    {
        var vertex = Call("Vertex", Id("G"));
        var step = All("x", vertex, All("y", vertex,
            Imp(Call("Adj", Graph(Id("G")), Id("x"), Id("y")),
                Le(Call("level", Id("x")), Add(Call("level", Id("y")), D(1))))));
        var interior = All("x", vertex, Imp(Lt(Call("level", Id("x")), Id("N")),
            Le(D(2), At(Graph(Id("G")), Id("x")))));
        var budget = All("v", Id("V"), Le(Demand, At(Graph(Id("G")), Image(Id("v")))));
        var margin = All("v", Id("V"), Lt(Add(Call("level", Image(Id("v"))), Id("l")), Id("N")));
        var body = Imp(step, Imp(interior, Imp(budget, Imp(margin,
            Call("HasExtension", Id("m"), Id("l"), Id("c"))))));
        var parameters = All("m", Fn(Id("V"), Nat), All("l", Nat, All("G", Call("Host"),
            All("c", Copy(Id("H"), Graph(Id("G"))), All("level", Fn(vertex, Nat), All("N", Nat, body))))));
        return Disp(Finite("V", All("H", Call("SimpleGraph", Id("V")), Imp(Call("IsTree", Id("H")), parameters))));
    }
    private static Formula TotalFormula()
    {
        var dead = All("c", Copy(Id("H"), Graph(Id("S"))),
            Call("Dead", Id("m"), Id("l"), Id("c")));
        var confining = And(Call("Nonempty", Copy(Id("H"), Graph(Id("S")))), dead);
        var result = Ex("S", Call("Host"),
            And(Call("Nonempty", Copy(Graph(Id("T")), Graph(Id("S")))), confining));
        var total = All("T", Call("Host"), Imp(Call("Nonempty", Copy(Id("H"), Graph(Id("T")))), result));
        var degree = Lt(Add(Call("sum", Id("m")), D(2)), Call("maxDegree", Id("H")));
        return Disp(Finite("V", All("H", Call("SimpleGraph", Id("V")), Imp(Call("IsTree", Id("H")),
            All("m", Fn(Id("V"), Nat), All("l", Nat, Imp(degree, total)))))));
    }
}
