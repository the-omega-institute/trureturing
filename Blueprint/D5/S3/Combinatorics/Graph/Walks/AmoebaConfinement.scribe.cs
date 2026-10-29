using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class AmoebaConfinementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/AmoebaConfinement.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/gurvichkrncvyalyi2025amoebas");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Simultaneous extensions inside finite tree hosts imply deadness for every minimum-total-edge growth. A finite interval argument supplies a safe branching degree.",
        H("Ordinary Amoeba Extensions and Total-Edge Growth"),
        Blocks(
            Paragraph(Text(
                "The source is Gurvich, Krnc and Vyalyi, Growing Trees and Amoebas’ Replications, "
                + "arXiv:2401.07484v1/v2, DOI 10.1007/s00025-025-02421-6, Section 2 and Conjecture 1. "
                + "The predicates here are formal encodings of its ordinary finite-tree conventions. "
                + "H is a finite simple undirected tree and m assigns a nonnegative integer to each vertex. "
                + "The number of roots is the sum of m, including multiplicity. A Host packages a finite vertex type, "
                + "its simple graph and connectedness and acyclicity. Copy means an injective graph homomorphism, "
                + "so its image is an actual subgraph isomorphic to H. Different copy maps retain different placements of m. "
                + "Containment is expressed by an injective homomorphism, allowing vertex relabeling. Coincidence is tested against that very "
                + "containing map, rather than against an unrelated isomorphism: it must cover all vertices and reflect every edge. "
                + "Thus no additional vertex or edge can remain outside the original containing image. The finite host convention is supported "
                + "by the published Lemma 3 and Theorem 4 and by the directly cited predecessor Avoidability beyond paths, DOI 10.37236/13023, "
                + "Section 2; the main paper gives no blanket sentence declaring all graphs finite.")),
            Node("HasExtension", "All arms are present simultaneously", ExtensionFormula(),
                "The extension graph has the original vertices and new vertices (v,a,j), with a below m(v) and j below l. "
                + "Original edges are preserved, v is adjacent to (v,a,0), and consecutive j values on each arm are adjacent. "
                + "An injective homomorphism of this entire graph, agreeing with the prescribed copy on H, realizes every arm together. "
                + "It forces all new vertices outside the copy and mutually distinct. Each arm has l edges; for l=0 it has no new vertices.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("MinimumGrowth", "The objective counts total edges", GrowthFormula(),
                "For a specified copy c in G and containing map i into S, the extension must be realized in S over i composed with c. "
                + "Every competing finite tree R and every containing map j are compared using the total number of edges. "
                + "No choice of a preferred minimizer or number of newly added edges is substituted.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Dead", "Every minimizing growth coincides", DeadFormula(),
                "Coincides(i) says that i is surjective on vertices and reflects adjacency as well as preserving it. "
                + "Thus it identifies the entire containing tree with the original host. Deadness quantifies all minimizing hosts and containing maps.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("TotallyConfined", "Every initial tree has a confining supertree", TotalFormula(),
                "A confining host admits a copy and every copy in it is dead, with multiplicities transported by that copy map. "
                + "Total confinement starts with any finite tree admitting a copy, preserves that initial tree by an injective graph map, "
                + "and requires a confining finite host. All lengths and zero multiplicities are retained. "
                + "This definition states the target property; the two lemmas below do not establish its universal existence assertion.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("dead_of_hasExtension", "An existing extension kills every minimum growth", DeadBridgeFormula(),
                "The current host itself competes in the total-edge minimum. A minimizing containing tree therefore has at most as many edges. "
                + "A finite tree has one fewer edge than vertices, so the containing map must be surjective. "
                + "Its injective map on undirected edge sets is also surjective, which supplies adjacency reflection. "
                + "This proves the assertion for every minimizer, including the zero-length and zero-multiplicity cases.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("exists_safe_degree", "A degree outside every demand interval", SafeDegreeFormula(),
                "The union of the integer intervals from d(v) inclusive to d(v)+m(v) exclusive has size at most the sum k of m. "
                + "There are k+1 integers from 2 through k+2. One avoids the union. Whenever d(v) is at most that integer q, "
                + "avoiding the interval implies d(v)+m(v) is at most q. This supplies a branching capacity, "
                + "and asserts neither the construction of a host nor disjoint path existence.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("amoeba-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), op, Seq(Open, b, Close));
    private static Formula Nat => Call("Nat");
    private static Formula Id(string name) => F.Id(name);
    private static Formula Graph(Formula x) => Call("graph", x);
    private static Formula Copy(Formula a, Formula b) => Call("Copy", a, b);
    private static Formula Ext(Formula c) => Call("HasExtension", Id("m"), Id("l"), c);
    private static Formula Base(Formula body) => All("V", Call("Type"),
        All("H", Call("SimpleGraph", Id("V")),
        All("m", Seq(Id("V"), Sp, To, Sp, Nat), All("l", Nat, body))));
    private static Formula HostCopy(Formula body) => Base(All("G", Call("Host"),
        All("c", Copy(Id("H"), Graph(Id("G"))), body)));

    private static Formula ExtensionFormula()
    {
        var agreement = All("v", Id("V"), Eq(Call("e", Call("inl", Id("v"))), Call("c", Id("v"))));
        var extension = Some("e", Copy(Call("extensionGraph", Id("H"), Id("m"), Id("l")), Id("G")), agreement);
        return Disp(Base(All("W", Call("Type"), All("G", Call("SimpleGraph", Id("W")),
            All("c", Copy(Id("H"), Id("G")), Iff(Ext(Id("c")), extension))))));
    }
    private static Formula GrowthFormula()
    {
        var minimum = All("R", Call("Host"), All("j", Copy(Graph(Id("G")), Graph(Id("R"))),
            Imp(Ext(Call("comp", Id("j"), Id("c"))), Le(Call("edgeCount", Id("S")), Call("edgeCount", Id("R"))))));
        var law = Iff(Call("MinimumGrowth", Id("m"), Id("l"), Id("c"), Id("i")),
            And(Ext(Call("comp", Id("i"), Id("c"))), minimum));
        return Disp(HostCopy(All("S", Call("Host"), All("i", Copy(Graph(Id("G")), Graph(Id("S"))), law))));
    }
    private static Formula DeadFormula() => Disp(HostCopy(Iff(Call("Dead", Id("m"), Id("l"), Id("c")),
        All("S", Call("Host"), All("i", Copy(Graph(Id("G")), Graph(Id("S"))),
            Imp(Call("MinimumGrowth", Id("m"), Id("l"), Id("c"), Id("i")), Call("Coincides", Id("i"))))))));
    private static Formula TotalFormula() => Disp(Base(Iff(Call("TotallyConfined", Id("H"), Id("m"), Id("l")),
        All("T", Call("Host"), Imp(Call("Nonempty", Copy(Id("H"), Graph(Id("T")))),
            Some("S", Call("Host"), And(Call("Nonempty", Copy(Graph(Id("T")), Graph(Id("S")))),
                Call("Confining", Id("H"), Id("m"), Id("l"), Id("S")))))))));
    private static Formula DeadBridgeFormula() => Disp(HostCopy(
        Imp(Ext(Id("c")), Call("Dead", Id("m"), Id("l"), Id("c")))));
    private static Formula SafeDegreeFormula()
    {
        var capacity = All("v", Id("V"), Imp(Le(Call("d", Id("v")), Id("q")),
            Le(Seq(Call("d", Id("v")), Sp, Plus, Sp, Call("m", Id("v"))), Id("q"))));
        var bounds = And(Le(D(2), Id("q")),
            And(Le(Id("q"), Seq(Call("sum", Id("m")), Sp, Plus, Sp, D(2))), capacity));
        var degree = All("d", Seq(Id("V"), Sp, To, Sp, Nat),
            All("m", Seq(Id("V"), Sp, To, Sp, Nat), Some("q", Nat, bounds)));
        return Disp(All("V", Call("Type"),
            Seq(OpenBracket, Call("Fintype", Id("V")), CloseBracket, Sp, degree)));
    }
}
