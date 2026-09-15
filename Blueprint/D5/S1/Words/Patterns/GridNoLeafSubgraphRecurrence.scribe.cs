using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns;

internal sealed class GridNoLeafSubgraphRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/kagey2018a301976");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Barker's recurrence and Kagey's modulo-ten congruence for no-leaf subgraphs of the three-by-n grid.",
        H("No-Leaf Subgraphs of the Three-by-n Grid"),
        Blocks(
            Paragraph(Text(
                "Vertices are pairs in Fin(3) times Fin(n). An Edge(n) value records its "
                + "lower or left column and one of five labels. Labels zero and one are the "
                + "two vertical edges in that column; labels two, three, and four are the "
                + "horizontal edges in rows zero, one, and two. Horizontal labels are absent "
                + "in the final column.")),
            Paragraph(Text(
                "A selected edge set is spanning because all vertices remain in the graph. "
                + "NoLeaf permits isolated vertices and excludes exactly the vertices of "
                + "degree one. The sequence a counts all selected edge sets satisfying that "
                + "condition.")),
            Node("Edge", "Canonical grid-edge labels", EdgeFormula(),
                "This is the literal subtype of column-label pairs satisfying the vertical "
                + "or horizontal validity condition.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("instFintypeEdge", "The edge labels form a finite type", FintypeFormula(),
                "The instance uses the filtered universe of Fin(n) times Fin(5); its members "
                + "are exactly the values of Edge(n).", DescribeRole.Definition,
                AssessedProvenance.FromRepo()),
            Node("gridEdges", "The complete grid-edge set", GridEdgesFormula(),
                "The complete edge set is the finite universe of Edge(n).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("degree", "Incident selected-edge count", DegreeFormula(),
                "The predicate is written directly from the five edge labels. Vertical label "
                + "k joins rows k and k+1 in its column. Horizontal label k joins row k-2 "
                + "in its recorded column to the next column.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("NoLeaf", "No vertex has degree one", NoLeafFormula(),
                "The predicate ranges over every vertex in Fin(3) times Fin(n); degree zero "
                + "is allowed.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("a", "The no-leaf subgraph count", SequenceFormula(),
                "The powerset ranges over all spanning edge-subgraphs, and the filter retains "
                + "exactly those satisfying NoLeaf.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("barker_a301976", "Barker's order-four recurrence", BarkerFormula(),
                "A bijection sends edge sets to compatible column-mask paths. Their eight-state "
                + "transfer recurrence satisfies the displayed order-four identity, which gives "
                + "the result after the path count is identified with a(n).",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a301976-grid-no-leaf-recurrence"),
                    ResolutionKind.Proved)),
            Node("kagey_a301976_mod10", "Kagey's modulo-ten congruence", KageyFormula(),
                "The initial residues at indices three through six are three. Strong induction "
                + "then applies Barker's recurrence modulo ten.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a301976-grid-no-leaf-mod-ten"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a301976-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula EdgeFormula()
    {
        var n = F.Id("n");
        var p = F.Id("p");
        var pairType = Product(Fin(n), Fin(D(5)));
        var vertical = Less(LabelOfPair(p), D(2));
        var horizontal = Less(Add(Value(ColumnOfPair(p)), D(1)), n);
        var subtype = Seq(OpenBrace, p, Colon, Sp, pairType, Sp, Mid, Sp,
            Or(vertical, horizontal), CloseBrace);
        return Disp(All([Bound("n", Naturals())], Equal(Edge(n), subtype)));
    }

    private static Formula FintypeFormula()
    {
        var n = F.Id("n");
        return Disp(All([Bound("n", Naturals())], Call("Fintype", Edge(n))));
    }

    private static Formula GridEdgesFormula()
    {
        var n = F.Id("n");
        return Disp(All([Bound("n", Naturals())],
            Equal(Call("gridEdges", n), Call("univ", Edge(n)))));
    }

    private static Formula DegreeFormula()
    {
        var n = F.Id("n");
        var h = F.Id("H");
        var x = F.Id("x");
        var e = F.Id("e");
        var label = LabelOfEdge(e);
        var column = ColumnOfEdge(e);
        var verticalEndpoints = Or(
            Equal(x, Pair(label, column)),
            Equal(x, Pair(Add(label, D(1)), column)));
        var row = Subtract(label, D(2));
        var horizontalEndpoints = Or(
            Equal(x, Pair(row, column)),
            Equal(x, Pair(row, Add(Value(column), D(1)))));
        var incident = Call("if", Less(label, D(2)),
            Parenthesized(verticalEndpoints), Parenthesized(horizontalEndpoints));
        var selectedIncident = Call("filter", Lambda(e, incident), h);
        return Disp(All([
            Bound("n", Naturals()),
            Bound("H", Finset(Edge(n))),
            Bound("x", Product(Fin(D(3)), Fin(n)))
        ], Equal(Call("degree", h, x), Call("card", selectedIncident))));
    }

    private static Formula NoLeafFormula()
    {
        var n = F.Id("n");
        var h = F.Id("H");
        var x = F.Id("x");
        var everyVertex = All([Bound("x", Product(Fin(D(3)), Fin(n)))],
            NotEqual(Call("degree", h, x), D(1)));
        return Disp(All([
            Bound("n", Naturals()),
            Bound("H", Finset(Edge(n)))
        ], Iff(Call("NoLeaf", h), Parenthesized(everyVertex))));
    }

    private static Formula SequenceFormula()
    {
        var n = F.Id("n");
        var h = F.Id("H");
        var candidates = Call("powerset", Call("gridEdges", n));
        var accepted = Call("filter", Lambda(h, Call("NoLeaf", h)), candidates);
        return Disp(All([Bound("n", Naturals())],
            Equal(Call("a", n), Call("card", accepted))));
    }

    private static Formula BarkerFormula()
    {
        var n = F.Id("n");
        var rhs = Subtract(
            Subtract(
                Subtract(Multiply(D(1, 2), IntA(n, 1)), Multiply(D(6), IntA(n, 2))),
                Multiply(D(2, 0), IntA(n, 3))),
            Multiply(D(5), IntA(n, 4)));
        return Disp(All([Bound("n", Naturals())], Implies(
            Less(D(4), n), Equal(Call("int", Call("a", n)), rhs))));
    }

    private static Formula KageyFormula()
    {
        var n = F.Id("n");
        return Disp(All([Bound("n", Naturals())], Implies(
            Less(D(2), n), Equal(new Formula.Modulo(Call("a", n), D(1, 0)), D(3)))));
    }

    private static Formula Naturals() => F.Id("N");
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Edge(Formula n) => Call("Edge", n);
    private static Formula Finset(Formula type) => Call("Finset", type);
    private static Formula Product(Formula left, Formula right) =>
        Seq(left, Sp, Times, Sp, right);
    private static Formula Value(Formula value) => Call("val", value);
    private static Formula ColumnOfPair(Formula pair) => Call("fst", pair);
    private static Formula LabelOfPair(Formula pair) => Value(Call("snd", pair));
    private static Formula EdgeValue(Formula edge) => Value(edge);
    private static Formula ColumnOfEdge(Formula edge) => ColumnOfPair(EdgeValue(edge));
    private static Formula LabelOfEdge(Formula edge) => LabelOfPair(EdgeValue(edge));
    private static Formula Pair(Formula first, Formula second) => Call("pair", first, second);
    private static Formula IntA(Formula n, byte offset) =>
        Call("int", Call("a", Subtract(n, D(offset))));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Lambda(Formula variable, Formula body) =>
        Parenthesized(Seq(variable, Sp, Mapsto, Sp, body));
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula All(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
