using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class FixedForestSlotGraphDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete-history incidence gives the exact original directed slot statistics.",
        H("Shared rows and directed edge multiplicity"),
        Blocks(
            Paragraph(Text(
                "The slot of a history is its assigned read target and absolute digit. "
                + "A nonroot history indexes the directed edge from its unique parent's slot. "
                + "Incoming degree counts distinct source rows, while edge multiplicity counts "
                + "complete-history preimages. Multiple input visits do not add edge preimages. "
                + "The two shared rows are w={H,K} and v={H1,K1}; they are distinct. "
                + "Read-control cycles and the allowed T=Q case remain unrestricted.")),
            Result("raw_history_surplus", "raw-history-surplus", "Full nonroot history accounting",
                RawScope(All("row", Call("Function", V("Node"), V("S")),
                    EqF(Call("historySurplus", V("F"), V("row")),
                        Seq(Call("rawJ", V("F"), V("row")), Plus,
                            Call("rawXi", V("F"), V("row")))))),
                "Partition nonroot histories by directed edge and partition distinct edges by their target row. "
                + "The sum of fiber cardinal minus one equals domain cardinal minus image cardinal. "
                + "The resulting identity uses complete histories and has no graph acyclicity premise."),
            Result("rawRows_map", "raw-rows-map", "Exact row-image transport",
                MapScope(EqF(Call("rawRows", V("F"), Call("compose", V("f"), V("row"))),
                    Call("image", V("f"), Call("rawRows", V("F"), V("row"))))),
                "Changing the row carrier maps precisely the nonroot history row image. No surjectivity is needed."),
            Result("rawEdges_map", "raw-edges-map", "Exact edge-image transport",
                MapScope(EqF(Call("rawEdges", V("F"), Call("compose", V("f"), V("row"))),
                    Call("image", Call("productMap", V("f"), V("f")), Call("rawEdges", V("F"), V("row"))))),
                "Both endpoints of every original history edge are mapped, with the same finite nonroot domain."),
            Result("rawJ_map", "raw-j-map", "Incoming-degree transport",
                MapScope(Imp(Call("Injective", V("f")),
                    EqF(Call("rawJ", V("F"), Call("compose", V("f"), V("row"))),
                        Call("rawJ", V("F"), V("row"))))),
                "Injectivity preserves each incoming-edge fiber under the product map. Its image cardinal is unchanged, "
                + "and summing over the exact row image preserves the indegree surplus."),
            Result("rawXi_map", "raw-xi-map", "History edge-fiber transport",
                MapScope(Imp(Call("Injective", V("f")),
                    EqF(Call("rawXi", V("F"), Call("compose", V("f"), V("row"))),
                        Call("rawXi", V("F"), V("row"))))),
                "The nonroot histories mapping to an injected edge are exactly the original edge fiber. "
                + "Their cardinalities and the sum over the finite edge image remain equal."),
            Result("rawJ_placement", "raw-j-placement", "Canonical and raw incoming statistics agree",
                Scope(All("alpha", Call("Assignment", V("F"), V("R"), V("e")),
                    EqF(Call("rawJ", V("F"), Call("placement", V("F"), V("R"), V("alpha"))),
                        Call("J", V("F"), V("R"), V("alpha"))))),
                "Edges ending at a row are in bijection with its distinct predecessor rows. "
                + "Rows outside the nonroot image have no incoming edges and contribute zero."),
            Result("rawXi_placement", "raw-xi-placement", "Canonical and raw repetition statistics agree",
                Scope(All("alpha", Call("Assignment", V("F"), V("R"), V("e")),
                    EqF(Call("rawXi", V("F"), Call("placement", V("F"), V("R"), V("alpha"))),
                        Call("Xi", V("F"), V("R"), V("alpha"))))),
                "The canonical edge preimage is exactly the raw nonroot history fiber. "
                + "Edges outside the finite edge image have empty fibers and contribute zero."),
            Result("shared_rows_distinct", "shared-rows-distinct", "The prescribed double rows differ",
                Assigned(Seq(Call("placement", V("F"), V("R"), V("alpha"), Call("H", V("R"))),
                    Neq, Call("placement", V("F"), V("R"), V("alpha"), Call("H1", V("R"))))),
                "Compatibility and the four distinct marked nodes exclude equality of the two prescribed rows."),
            Result("raw_fibers_only", "raw-fibers-only", "The original surpluses exclude every additional collision",
                PrescribedScope(All("S", V("Type"), All("eqS", Call("DecidableEq", V("S")),
                    All("row", Call("Function", V("Node"), V("S")),
                    Nodes(Imp(Call("prescribedRawHypotheses", V("F"), V("R"), V("row"), V("n"), V("m")),
                        Call("Shared", V("F"), V("R"), V("n"), V("m")))))))),
                "For any row carrier with decidable equality, the H/K and H1/K1 pairs occupy distinct rows. "
                + "If rawJ=rawXi=1, their two fiber excesses exhaust the total. Every nonroot "
                + "equal-row pair is therefore exactly one of the prescribed pairs, or an identical node. "
                + "The hypotheses are row(H)=row(K), row(H1)=row(K1), row(H) unequal row(H1), "
                + "rawJ=rawXi=1, nonroot n and m, and row(n)=row(m)."),
            Result("repeated_edge_only", "repeated-edge-only", "The sole repeated edge",
                Assigned(Nodes(Imp(Call("sameNonrootEdge", V("F"), V("R"), V("alpha"), V("n"), V("m")),
                    Call("equalOrResolvingPair", V("R"), V("n"), V("m"))))),
                "Equal directed edges with distinct forest preimages can only be H1/K1. "
                + "H/K have distinct binary source rows; H1/K1 have the same source row w and target row v."),
            Result("incoming_excess", "incoming-excess", "J equals one",
                Assigned(EqF(Call("J", V("F"), V("R"), V("alpha")), D(1))),
                "Only w has two incoming source rows. Every other used row has at most one; "
                + "roots and unused rows contribute zero to the sum of incoming degree minus one."),
            Result("repetition_excess", "repetition-excess", "Xi equals one",
                Assigned(EqF(Call("Xi", V("F"), V("R"), V("alpha")), D(1))),
                "The edge w to v has exactly two complete-history preimages. Every other edge has at most one."),
            Result("sharing_excess", "sharing-excess", "Binary sharing equals one",
                Scope(All("alpha", Call("Assignment", V("F"), V("R"), V("e")),
                    EqF(Call("sharing", V("F"), V("R"), V("alpha")), D(1)))),
                "A/B are the only merged binary target. All other binary parents represent separate targets. "
                + "This counts histories and also covers H=A or H=B."))));

    private static Formula V(string name) => F.Id(name);
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Sp, Grp(V(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula EqF(Formula a, Formula b) => Seq(a, Eq, b);
    private static Formula All(string n, Formula type, Formula body) =>
        Seq(Forall, Sp, V(n), Colon, type, Comma, Grp(body));
    private static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Implies, Grp(b));
    private static Formula AllN(string[] names, Formula body) =>
        names.Reverse().Aggregate(body, (b, n) => All(n, N, b));
    private static Formula ForestScope(Formula body) => AllN(["P", "h", "ell"],
        All("Node", V("Type"), All("finiteNode", Call("Fintype", V("Node")),
        All("eqNode", Call("DecidableEq", V("Node")), All("hP", Seq(D(1), Lt, V("P")),
        All("F", Call("PhysicalForest", V("P"), V("h"), V("ell"), V("Node"), V("hP")), body))))));
    private static Formula Scope(Formula body) => ForestScope(All("e", N,
        All("R", Call("Prescribed", V("F")), body)));
    private static Formula PrescribedScope(Formula body) => ForestScope(
        All("R", Call("Prescribed", V("F")), body));
    private static Formula RawScope(Formula body) => ForestScope(
        All("S", V("Type"), All("eqS", Call("DecidableEq", V("S")), body)));
    private static Formula MapScope(Formula body) => RawScope(
        All("T", V("Type"), All("eqT", Call("DecidableEq", V("T")),
        All("row", Call("Function", V("Node"), V("S")),
        All("f", Call("Function", V("S"), V("T")), body)))));
    private static Formula Nodes(Formula body) =>
        All("n", V("Node"), All("m", V("Node"), body));
    private static Formula Assigned(Formula body) => Scope(
        All("alpha", Call("Assignment", V("F"), V("R"), V("e")),
            Imp(Call("Compatible", V("F"), V("R"), V("e")), body)));
    private static DocumentBlock Result(string declaration, string id, string heading,
        Formula statement, string explanation) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph." + declaration),
            H(heading), StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);
}
