using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeJ2HalfRestorationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2HalfRestoration.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Restoring the opposite three actual J2 cuts earns both native one-frame three-component partitions, including the literal barred exception.",
        H("Actual J2 Half-Cut Restoration"),
        Blocks(
            Definition("HalfCut", "The Selected Three Actual Cuts", CutFormula(),
                "HalfCut(m,side,e) holds precisely when e equals markedEdge(m,(i,side)) for an i in Fin(3)."),
            Definition("HalfEdge", "The Independent Half-Cut Edge Inventory", EdgeFormula(),
                "Keep the complete actual F2 native inventory outside the original T/E cuts together with the actual T/E seams, and remove only the three marked cuts with the selected side."),
            Definition("halfGraph", "The Actual Graph after Three Cuts", GraphFormula(),
                "halfGraph(m,side) is SimpleGraph.fromEdgeSet of HalfEdge(m,side). It contains the actual six-cut surviving graph and restores exactly the opposite three marked edges."),
            Definition("halfStart", "The Independent Half-Component Starting Ports", PortFormula(false),
                "For side false the starts are R0, L0 and R1; for side true they are bar R0, bar L1 and bar L2, in native index order."),
            Definition("halfFinish", "The Independent Half-Component Finishing Ports", PortFormula(true),
                "For side false the finishes are R2, L1 and L2; for side true they are bar R1, bar R2 and bar L0. The barred indices are retained literally."),
            Describe.Lean(DescribeId.Create("native-j2-half-component-partition"),
                DeclarationHandle.Create(Prefix + "native_j2_half_component_partition"),
                H("Both Actual Native Three-Component Partitions Exhaust F2 Exactly Once"),
                StatementSource.FromAuthor(ComponentFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every m at least five and either side, three actual simple paths connect the independently specified starting and finishing ports. Each path exhausts its complete reachable component and contains every actual edge incident to it. A configuration belongs to F2Domain(m) exactly when it belongs to the support of a unique path. The flattened edge lists contain an edge exactly when it belongs to the independent HalfEdge(m,side) inventory; therefore they are the retained inventory of any original native F2 Hamilton witness with that same exact full inventory.")),
                    Paragraph(Text(
                    "The six-cut partition supplies six actual component walks. Actual marked-edge injectivity proves that each of the opposite three marked edges is restored, while the selected three cuts remain missing. Concatenating those earned reachability bridges gives the independent pairs R0 to R2, L0 to L1 and R1 to L2 for side false, and bar R0 to bar R1, bar L1 to bar R2 and bar L2 to bar L0 for side true.")),
                    Paragraph(Text(
                    "The original actual F2 Hamilton cycle bounds the half-cut graph degree by two and makes all selected ports leaves. A simple reachable path is nonbacktracking, so the leaf-component theorem earns full vertex and edge exhaustion. Every one of the six old components is linked to a half-component root, which proves full F2 coverage. The selected leaves and independent endpoint table force uniqueness. The barred table keeps the native k equals two exception; it does not rename or reverse the base indexing."))), DescribeRole.Theorem))));

    private static DocumentBlock Definition(string selector, string title, Formula formula, string meaning) =>
        Describe.Lean(DescribeId.Create(selector.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + selector), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(meaning))), DescribeRole.Definition);

    private static Formula CutFormula()
    {
        Formula m = F.Id("m"), side = F.Id("side"), e = F.Id("e"), i = F.Id("i");
        return Disp(All("m", Call("Nat"), All("side", Call("Bool"),
            All("e", Call("Sym2", Call("Configuration", m)),
                Iff(Call("HalfCut", m, side, e), Some("i", Call("Fin", D(3)),
                    Eq(e, Call("markedEdge", m, Call("Tuple2", i, side)))))))));
    }

    private static Formula EdgeFormula()
    {
        Formula m = F.Id("m"), side = F.Id("side"), e = F.Id("e");
        return Disp(All("m", Call("Nat"), All("side", Call("Bool"),
            All("e", Call("Sym2", Call("Configuration", m)),
                Iff(Call("HalfEdge", m, side, e),
                    And(Or(And(Call("F2NativeEdge", m, e), Neg(Call("F2DeletedEdge", m, e))),
                        Call("F2Seam", m, e)), Neg(Call("HalfCut", m, side, e))))))));
    }

    private static Formula GraphFormula()
    {
        Formula m = F.Id("m"), side = F.Id("side"), x = F.Id("x"), y = F.Id("y");
        return Disp(All("m", Call("Nat"), All("side", Call("Bool"),
            All("x", Call("Configuration", m), All("y", Call("Configuration", m),
                Iff(Call("Adj", Call("halfGraph", m, side), x, y),
                    And(Call("HalfEdge", m, side, Call("Sym2Pair", x, y)), Neg(Eq(x, y)))))))));
    }

    private static Formula PortFormula(bool finish)
    {
        Formula side = F.Id("side"), i = F.Id("i");
        Formula Port(byte owner, bool barred, bool left) =>
            Call("Tuple3", D(owner), Call(barred ? "True" : "False"), Call(left ? "True" : "False"));
        Formula Table(Formula p0, Formula p1, Formula p2) =>
            Call("IfThenElse", Eq(Call("FinValue", i), D(0)), p0,
                Call("IfThenElse", Eq(Call("FinValue", i), D(1)), p1, p2));
        Formula unbarred = finish
            ? Table(Port(2, false, false), Port(1, false, true), Port(2, false, true))
            : Table(Port(0, false, false), Port(0, false, true), Port(1, false, false));
        Formula barred = finish
            ? Table(Port(1, true, false), Port(2, true, false), Port(0, true, true))
            : Table(Port(0, true, false), Port(1, true, true), Port(2, true, true));
        return Disp(All("side", Call("Bool"), All("i", Call("Fin", D(3)),
            Eq(Call(finish ? "halfFinish" : "halfStart", side, i),
                Call("IfThenElse", side, barred, unbarred)))));
    }

    private static Formula ComponentFormula()
    {
        Formula m = F.Id("m"), side = F.Id("side"), paths = F.Id("paths"), i = F.Id("i");
        Formula x = F.Id("x"), y = F.Id("y"), graph = Call("halfGraph", m, side);
        Formula Path(Formula index) => Call("apply", paths, index);
        Formula Start(Formula index) => Call("port", m, Call("halfStart", side, index));
        Formula Reach(Formula vertex) => Call("Reachable", graph, Start(i), vertex);
        Formula vertices = All("i", Call("Fin", D(3)), All("x", Call("Configuration", m),
            Iff(Call("Member", x, Call("Support", Path(i))), Reach(x))));
        Formula edges = All("i", Call("Fin", D(3)), All("x", Call("Configuration", m),
            All("y", Call("Configuration", m), Iff(And(Call("Adj", graph, x, y), Reach(x)),
                Call("Member", Call("Sym2Pair", x, y), Call("Edges", Path(i)))))));
        Formula j = F.Id("j");
        Formula unique = Some("i", Call("Fin", D(3)),
            And(Call("Member", x, Call("Support", Path(i))), All("j", Call("Fin", D(3)),
                Implies(Call("Member", x, Call("Support", Path(j))), Eq(j, i)))));
        Formula cover = All("x", Call("Configuration", m), Iff(Call("F2Domain", m, x), unique));
        Formula family = Call("DependentWalkFamily", Call("Fin", D(3)), graph,
            Call("HalfStartPortFamily", side), Call("HalfFinishPortFamily", side), m);
        Formula e = F.Id("e");
        Formula inventory = All("e", Call("Sym2", Call("Configuration", m)),
            Iff(Call("Member", e, Call("FlattenWalkEdges", paths)), Call("HalfEdge", m, side, e)));
        Formula body = Some("paths", family,
            And(All("i", Call("Fin", D(3)), Call("IsPath", Path(i))), And(vertices, And(edges, And(cover, inventory)))));
        return Disp(All("m", Call("Nat"), Implies(Le(D(5), m), All("side", Call("Bool"), body))));
    }

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Neg(Formula a) => new Formula.Not(a);
}
