using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeJ2FrameInventoryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameInventory.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One choice of the actual complete F2 Hamilton cycle is mapped once to any native two-label frame, preserving its full inventory and earning retained a/b edges for the actual k2 Q construction.",
        H("One Actual Frame Cycle With All Inventories"),
        Blocks(
            Node("frame-domain", "FrameDomain", "The Actual Independent Frame Layer",
                Eq(Call("FrameDomain", Frame()), Call("Layer", Call("ToFinset", Call("Selected", Frame())),
                    Call("CycleOfList", Call("Cons", Call("Terminal", Frame()), Call("Base", Frame()))))),
                "FrameDomain(F) is precisely Layer(F.selected.toFinset, F.terminal :: F.base). The mapped target is this actual layer; it is never identified by definition with the raw F2Domain.", DescribeRole.Definition),
            Node("undo-relabel", "undoRelabel", "Undo the Earned Frame Relabelling",
                Eq(Call("undoRelabel", Frame(), F.Id("x")),
                    Call("Multiply", Call("Inverse", Call("relabel", Frame())), F.Id("x"))),
                "Undo is left multiplication by the inverse of the same relabel(F) used by frameDomainIso. Full native-edge, deleted-edge and seam inventories are evaluated on the two ambient endpoints after this undo map.", DescribeRole.Definition),
            Node("one-frame-cycle-inventory", "native_j2_frame_cycle_with_inventory", "The Same Actual Mapped Cycle Earns Every Required Inventory",
                InventoryFormula(),
                "For every m at least five and every SupplyFrame(m,2), choose the already proved canonical actual F2 Hamilton witness only once and map it by frameDomainIso. The theorem returns both raw and mapped witnesses together with the raw Hamilton and full-inventory facts, identifies the mapped base, and identifies the mapped walk by heterogeneous equality. This exact mapped walk is Hamiltonian, has the full raw native-minus-deleted plus seam inventory after undo relabelling, and contains the images of all six independently specified marked edges. "
                + "The same walk also earns the actual native a-edge inventory: for frame vertices x,y with y=x*a, the edge is retained whenever its terminal-label pair differs from {rho(m),rho(0)}. The complete raw a-cut classification shows that both deleted a edges have terminal pair {0,m}; mapping the labels gives exactly the excluded pair. For y=x*b, every edge whose starting terminal lies outside F.selected.toFinset is retained, since the raw b-cut classification permits terminal zero or m only. These facts are conclusions earned from the selected witness, not supplied inventory premises. "
                + "The two labels p=rho(m), q=rho(0) are distinct and their set is exactly the two selected frame labels. In particular the a-edge claim does not allow p=q. The same graph isomorphism and raw witness remain available to transport the literal six slices and actual half-restoration paths before the exceptional k2 Q route. The theorem supplies a base witness and its inventories; the higher all-size recursive Hamilton closure remains a separate obligation. This combines existing F2 inventory, marked-edge and graph-map results with the complete native cut classifications.", DescribeRole.Theorem))));

    private static Formula InventoryFormula()
    {
        Formula m = F.Id("m"), w = F.Id("w"), x = F.Id("x"), y = F.Id("y"), e = F.Id("e");
        Formula rho = Call("relabel", Frame()), p = Call("Apply", rho, Call("Last", m)), q = Call("Apply", rho, D(0));
        Formula down = Call("Sym2Map", Call("undoRelabel", Frame()), e);
        Formula edges = Call("AmbientEdges", w);
        Formula selected = Call("ToFinset", Call("Selected", Frame()));
        Formula inventory = All("e", Call("Sym2", Call("Configuration", m)),
            Iff(Call("Member", e, edges), Or(And(Call("F2NativeEdge", m, down),
                Not(Call("F2DeletedEdge", m, down))), Call("F2Seam", m, down))));
        Formula marks = All("i", Call("Product", Call("Fin", D(3)), Call("Bool")),
            Call("Member", Call("Sym2Map", Call("LeftMultiply", rho), Call("markedEdge", m, F.Id("i"))), edges));
        Formula hA = All("x", Call("FrameVertex", Frame()), All("y", Call("FrameVertex", Frame()),
            Implies(And(Eq(Call("Value", y), Call("Multiply", Call("Value", x), Call("a", m))),
                Ne(Call("Sym2Pair", Call("LastLabel", x), Call("LastLabel", y)), Call("Sym2Pair", p, q))),
                Call("Member", Call("Sym2Pair", x, y), Call("Edges", w)))));
        Formula hB = All("x", Call("FrameVertex", Frame()), All("y", Call("FrameVertex", Frame()),
            Implies(And(Eq(Call("Value", y), Call("Multiply", Call("Value", x), Call("b", m))),
                Not(Call("Member", Call("LastLabel", x), selected))),
                Call("Member", Call("Sym2Pair", x, y), Call("Edges", w)))));
        Formula rawInventory = All("e", Call("Sym2", Call("Configuration", m)),
            Iff(Call("Member", e, Call("AmbientEdges", F.Id("rawWalk"))),
                Or(And(Call("F2NativeEdge", m, e), Not(Call("F2DeletedEdge", m, e))), Call("F2Seam", m, e))));
        Formula facts = And(Call("IsHamiltonianCycle", F.Id("rawWalk")), And(rawInventory, And(Eq(F.Id("base"), Call("Apply", Call("frameDomainIso", m, Frame()), F.Id("rawBase"))),
            And(Call("HEq", w, Call("WalkMap", F.Id("rawWalk"), Call("frameDomainIso", m, Frame()))),
            And(Call("IsHamiltonianCycle", w), And(inventory, And(marks, And(hA, And(hB,
                And(Ne(p, q), Eq(selected, Call("PairSet", p, q))))))))))));
        return Disp(All("m", Call("Nat"), Implies(Le(D(5), m), All("F", Call("SupplyFrame", m, D(2)),
            Exists("rawBase", Call("F2Vertex", m), Exists("rawWalk", Call("F2ClosedWalk", m, F.Id("rawBase")),
                Exists("base", Call("FrameVertex", Frame()), Exists("w", Call("FrameClosedWalk", Frame(), F.Id("base")), facts))))))));
    }
    private static DocumentBlock Node(string id, string declaration, string title, Formula statement, string meaning, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(meaning))), role);
    private static Formula Frame() => F.Id("F");
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => Not(Eq(a,b));
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Not(Formula a) => new Formula.Not(a);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
}
