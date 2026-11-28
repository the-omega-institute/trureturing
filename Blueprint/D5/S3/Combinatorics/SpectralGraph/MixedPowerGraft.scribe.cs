using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class MixedPowerGraftDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/MixedPowerGraft.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/dasashnisangeetha2026graphpowers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A terminal-leaf transfer weakly decreases the mixed largest eigenvalue. The final transfer to a path is strict under the stated hypotheses.",
        H("Terminal-leaf transfers for powered graphs"),
        Blocks(
            Node("adjacency", "Power adjacency", "graphPower_adj_dist_iff", Adjacency(),
                "On a connected graph, extended distance agrees with the natural-valued shortest-path distance."),
            Node("connected", "Connected powers", "graphPower_connected", ConnectedPower(),
                "Every edge of the original graph is present in each positive power."),
            Node("weak-transfer", "Weak comparison for pendant arms", "mixedTop_move_le", Pendant(false),
                "Reflect coordinates on the path between the two attachment points. Pair and off-path energy comparisons preserve the Rayleigh bound."),
            Node("strict-transfer", "Strict final transfer for powers at least two", "mixedTop_last_move_lt",
                Pendant(true), "A fixed off-path incidence in the old power is missing from the path power. Its mixed energy is strictly positive on a positive maximizing vector."),
            Node("first-power-transfer", "Strict final transfer for the first power",
                "mixedTop_last_graft_one_lt", FirstPower(),
                "If the top values agree, both vectors satisfy their maximizing eigenvector equations. For the three possible orders of the attachment coordinates, the moved leaf row, opposite-arm row, and old attachment row give contradictions, respectively.")),
        []));

    private static DocumentBlock Node(string id, string title, string name, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Qualified(name), [.. args]);

    private static Formula Qualified(string name) =>
        Seq(Operatorname, Grp(Seq(name.Split('.').SelectMany((part, index) =>
            index == 0 ? new Formula[] { F.Id(part) } : [Dot, F.Id(part)]).ToArray())));
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Type() => Seq(Qualified("Type"), Sp, F.Id("u"));
    private static Formula Bind(Formula name, Formula domain, Formula body) =>
        Seq(Forall, Sp, Par(Seq(name, Sp, Colon, Sp, domain)), Comma, Sp, body);
    private static Formula All(string name, Formula domain, Formula body) => Bind(F.Id(name), domain, body);
    private static Formula Instance(Formula domain, Formula body) =>
        Seq(Forall, Sp, OpenBracket, domain, CloseBracket, Comma, Sp, body);
    private static Formula Relation(Formula left, Formula op, Formula right) => Seq(left, Sp, op, Sp, right);
    private static Formula Imp(Formula premise, Formula body) => Relation(Par(premise), To, body);
    private static Formula Power(Formula graph, Formula k) =>
        Call("D5.S3.Combinatorics.Graph.ZeroForcing.GridPowerZeroForcingRefutation.graphPower", graph, k);
    private static Formula Top(Formula graph, Formula k) =>
        Call("OmegaMath.MixedAdjacency.mixedTop", Power(graph, k), Alpha);
    private static Formula IsoPath(Formula graph) => Call("Nonempty",
        Call("SimpleGraph.Iso", graph, Call("SimpleGraph.pathGraph", Call("Fintype.card", F.Id("V")))));
    private static Formula AlphaRange(bool strict, Formula body) =>
        Bind(Alpha, Real(), Imp(Relation(D(0), Le, Alpha), Imp(Relation(Alpha, strict ? Lt : Le, D(1)), body)));

    private static Formula Adjacency()
    {
        var v = F.Id("V");
        var g = F.Id("G");
        var i = F.Id("i");
        var j = F.Id("j");
        var k = F.Id("k");
        var rhs = Relation(Relation(i, Neq, j), Land, Relation(Call("SimpleGraph.dist", g, i, j), Le, k));
        return All("V", Type(), All("G", Call("SimpleGraph", v), Imp(Call("SimpleGraph.Connected", g),
            All("k", Qualified("Nat"), All("i", v, All("j", v,
                Relation(Call("SimpleGraph.Adj", Power(g, k), i, j), Iff, rhs)))))));
    }

    private static Formula ConnectedPower()
    {
        var v = F.Id("V");
        var g = F.Id("G");
        var k = F.Id("k");
        return All("V", Type(), All("G", Call("SimpleGraph", v), Imp(Call("SimpleGraph.Connected", g),
            All("k", Qualified("Nat"), Imp(Relation(D(1), Le, k), Call("SimpleGraph.Connected", Power(g, k)))))));
    }

    private static Formula Pendant(bool strict)
    {
        var v = F.Id("V");
        var t = F.Id("T");
        var k = F.Id("k");
        var a = F.Id("a");
        var b = F.Id("b");
        var x = F.Id("X");
        var y = F.Id("Y");
        var hb = F.Id("hb");
        var hab = F.Id("hab");
        var hbLeA = Call("LE.le.trans", hb, hab);
        var move = Call("OmegaMath.TreeGraft.PendantArm.move", x, y, hb);
        var comparison = AlphaRange(strict, Relation(Top(move, k), strict ? Lt : Le, Top(t, k)));
        var lowerK = Relation(D(strict ? (byte)2 : (byte)1), Le, k);
        var order = Relation(Seq(k, Sp, Plus, Sp, D(2)), Le, Call("Fintype.card", v));
        var props = All("k", Qualified("Nat"), Imp(lowerK, strict ? Imp(order, comparison) : comparison));
        if (strict)
            props = Imp(Seq(Neg, IsoPath(t)), Imp(IsoPath(move), props));
        var distinct = Relation(Call("OmegaMath.TreeGraft.PendantArm.first", x, hbLeA), Neq,
            Call("OmegaMath.TreeGraft.PendantArm.first", y, hb));
        var domain = Qualified("Nat");
        var vertex = F.Id("z");
        return All("V", Type(), All("T", Call("SimpleGraph", v), All("z", v,
            Instance(Call("Fintype", v), Instance(Call("DecidableRel", Call("SimpleGraph.Adj", t)),
                All("a", domain, All("b", domain,
                    All("X", Call("OmegaMath.TreeGraft.PendantArm", t, vertex, a),
                        All("Y", Call("OmegaMath.TreeGraft.PendantArm", t, vertex, b),
                            Instance(Call("DecidableEq", v),
                                Imp(Call("SimpleGraph.IsTree", t), All("hb", Relation(D(1), Le, b),
                                    All("hab", Relation(b, Le, a), Imp(distinct, props))))))))))))));
    }

    private static Formula FirstPower()
    {
        var v = F.Id("V");
        var t = F.Id("T");
        var z = F.Id("z");
        var l = F.Id("L");
        var arms = F.Id("A");
        var tip = Call("Subtype.val", Call("OmegaMath.TreeGraft.TerminalArms.q", arms, Call("Fin.last", l)));
        var graft = Call("OmegaMath.TreeGraft.graft", t, z, tip);
        var compare = AlphaRange(true, Relation(Top(graft, D(1)), Lt, Top(t, D(1))));
        return All("V", Type(), Instance(Call("Fintype", v), Instance(Call("DecidableEq", v),
            All("T", Call("SimpleGraph", v), All("z", v, All("L", Qualified("Nat"),
                Instance(Call("DecidableRel", Call("SimpleGraph.Adj", t)),
                    All("A", Call("OmegaMath.TreeGraft.TerminalArms", t, z, l),
                        Imp(Call("SimpleGraph.IsTree", t), Imp(Seq(Neg, IsoPath(t)), Imp(IsoPath(graft), compare)))))))))));
    }
}
