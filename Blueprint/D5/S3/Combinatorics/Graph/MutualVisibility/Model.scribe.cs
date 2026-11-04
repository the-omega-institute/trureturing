using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.MutualVisibility;

internal sealed class ModelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/MutualVisibility/Model.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/fresanfigueroa2026mutualvisibility");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original-host mutual visibility and the auxiliary geometry of the full mixed reconfiguration graph.",
        H("The source model and separator conventions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("configuration-decidable-equality"),
                DeclarationHandle.Create(Prefix + "configurationDecidableEq"),
                H("Equality of configurations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Classical equality on the subtype of feasible finite subsets supports the finite cut interface."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("visible"),
                DeclarationHandle.Create(Prefix + "Visible"),
                H("Mutual visibility in the original host"),
                StatementSource.FromAuthor(VisibleFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every pair of distinct selected endpoints there exists a shortest walk in the original host, and any selected vertex on its support is an endpoint. A minimum-length walk is a path, so this is the source geodesic definition. The chosen path may differ between endpoint pairs."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mixedmove"),
                DeclarationHandle.Create(Prefix + "MixedMove"),
                H("Both source move rules"),
                StatementSource.FromAuthor(MoveFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Distinct finite sets are joined by one-vertex symmetric difference, or by singleton set differences whose removed and inserted labels are adjacent in the actual host. The latter label is unoccupied before the slide. No fixed rank or unrestricted token swap is substituted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("configuration"),
                DeclarationHandle.Create(Prefix + "Configuration"),
                H("The complete feasible family"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A configuration is a finite subset together with its mutual-visibility proof. The empty set, every feasible rank, and both small host orders are retained."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reconfiguration"),
                DeclarationHandle.Create(Prefix + "reconfiguration"),
                H("The full mixed graph"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Vertices are all configurations and adjacency is exactly MixedMove. Symmetry comes from undirected host adjacency and from symmetric difference; distinct endpoints exclude loops."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("configurationfintype"),
                DeclarationHandle.Create(Prefix + "configurationFintype"),
                H("Finiteness of the configuration family"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a finite host, all configurations form a finite subtype of the finite powerset."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reconfigurationdecidableadj"),
                DeclarationHandle.Create(Prefix + "reconfigurationDecidableAdj"),
                H("Decidable finite adjacency"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Classical decidability supplies the finite-graph degree interface without replacing the mathematical move predicate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("visible-mono"),
                DeclarationHandle.Create(Prefix + "visible_mono"),
                H("Hereditary visibility"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Proposition 2.1 of Fresán-Figueroa, Goldfeder and Lozano-Piña states hereditary mutual visibility and attributes it to Cicerone et al. (2023), Variety of mutual-visibility problems in graphs. A geodesic avoiding the other vertices of a larger selected set also avoids the other vertices of each selected subset.")))),
            Describe.Lean(
                DescribeId.Create("visible-empty"),
                DeclarationHandle.Create(Prefix + "visible_empty"),
                H("The empty configuration"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The endpoint condition is vacuous for the empty set. It is present in the graph.")))),
            Describe.Lean(
                DescribeId.Create("visible-singleton"),
                DeclarationHandle.Create(Prefix + "visible_singleton"),
                H("Singleton configurations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("There are no distinct selected endpoints in a singleton.")))),
            Describe.Lean(
                DescribeId.Create("visible-pair"),
                DeclarationHandle.Create(Prefix + "visible_pair"),
                H("All pairs of a connected host"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Connectedness supplies a shortest original-host walk. A selected pair has no third selected label to avoid.")))),
            Describe.Lean(
                DescribeId.Create("mixedmove-insert"),
                DeclarationHandle.Create(Prefix + "mixedMove_insert"),
                H("Token addition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Inserting a previously unoccupied label changes the symmetric difference by precisely that one label.")))),
            Describe.Lean(
                DescribeId.Create("mixedmove-erase"),
                DeclarationHandle.Create(Prefix + "mixedMove_erase"),
                H("Token removal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Erasing an occupied label is the reverse of its insertion.")))),
            Describe.Lean(
                DescribeId.Create("separates"),
                DeclarationHandle.Create(Prefix + "Separates"),
                H("Finite vertex separators"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A cut either leaves at most one vertex or makes the induced graph on all surviving vertices fail to be preconnected. The remaining graph is the actual induced graph, with both move types preserved."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("vertexconnectivity"),
                DeclarationHandle.Create(Prefix + "vertexConnectivity"),
                H("Vertex connectivity with complete-graph conventions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take the least cardinality of a separator. The whole vertex set always supplies a candidate. On a nonempty complete graph this convention gives its order minus one, and on a one-vertex graph it gives zero. The minimum-pair separator argument proves the matching lower bound for the full visibility graph."))),
                DescribeRole.Definition))));

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula HostScope(Formula body) => All("V", Call("Type"), Seq(
        OpenBracket, Call("DecidableEq", F.Id("V")), CloseBracket, Sp,
        All("H", Call("SimpleGraph", F.Id("V")), body)));

    private static Formula VisibleFormula()
    {
        Formula h = F.Id("H"), s = F.Id("S"), v = F.Id("V"), u = F.Id("u"),
            x = F.Id("v"), p = F.Id("p"), z = F.Id("z");
        Formula avoids = All("z", v, Imp(And(Mem(z, Call("support", p)), Mem(z, s)),
            Or(Eq(z, u), Eq(z, x))));
        Formula witness = Ex("p", Call("Walk", h, u, x),
            And(Eq(Call("length", p), Call("dist", h, u, x)), avoids));
        return Disp(All("V", Call("Type"), All("H", Call("SimpleGraph", v),
            All("S", Call("Finset", v), Iff(Call("Visible", h, s),
                All("u", v, Imp(Mem(u, s), All("v", v,
                    Imp(Mem(x, s), Imp(Ne(u, x), witness))))))))));
    }

    private static Formula MoveFormula()
    {
        Formula h = F.Id("H"), s = F.Id("S"), t = F.Id("T"), v = F.Id("V"),
            x = F.Id("x"), y = F.Id("y");
        Formula slide = Ex("x", v, Ex("y", v, And(
            Eq(Call("sdiff", s, t), Call("singleton", x)), And(
            Eq(Call("sdiff", t, s), Call("singleton", y)), Call("Adj", h, x, y)))));
        Formula move = And(Ne(s, t), Or(Eq(Call("card", Call("symmDiff", s, t)), D(1)), slide));
        return Disp(HostScope(All("S", Call("Finset", v), All("T", Call("Finset", v),
            Iff(Call("MixedMove", h, s, t), move)))));
    }
}
