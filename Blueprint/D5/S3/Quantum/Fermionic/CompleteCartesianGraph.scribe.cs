using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

#pragma warning disable IDE0051 // Shared DSL helper vocabulary intentionally exceeds each document formula set.
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class CompleteCartesianGraphDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/CompleteCartesianGraph.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Changing one coordinate gives a regular Cartesian product of complete graphs.",
        H("Cartesian products of finite complete graphs"),
        Blocks(
            Paragraph(Text("Nat is the natural-number type and Type is an arbitrary type. Fin(q) has q labels, Fun(A,B) is the function type A → B, and card denotes finite-type cardinality. SimpleGraphMk(R) denotes the simple graph with the displayed symmetric irreflexive adjacency relation R; its symmetry and irreflexivity proof fields are suppressed. edgeCount(G) is the cardinality of G.edgeFinset, counting each undirected edge once. tsub denotes natural subtraction truncated at zero. IsRegularOfDegree(G,D) means that every vertex of G has degree D. Fintype is the usual finite-type enumeration instance.")),
            Node("coordinateGraph", "One-coordinate adjacency", Definition(),
                "The adjacency relation says that x and y disagree at one coordinate a and agree at every other coordinate. This is exactly the Cartesian product of q copies of the complete graph on the alphabet type. The definition includes the empty-coordinate case.", DescribeRole.Definition),
            Node("regular_and_edge_count", "Degree and undirected edge count", Result(),
                "Each neighbour is uniquely specified by the coordinate to replace and by its replacement value, which differs from the old value. The degree-sum identity then counts undirected edges. The conclusion also holds for an empty alphabet and for zero coordinates.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role) => Describe.Lean(
        DescribeId.Create("fgauss-cartesian-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsIn(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula lhs, Formula rhs) =>
        new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs);
    private static Formula Ne(Formula lhs, Formula rhs) =>
        new Formula.Relation(lhs, FormulaRelationOperator.NotEqual, rhs);
    private static Formula Mul(Formula lhs, Formula rhs) =>
        new Formula.Binary(lhs, FormulaBinaryOperator.Multiply, rhs);
    private static Formula And(Formula lhs, Formula rhs) =>
        new Formula.Logic(Parenthesized(lhs), FormulaLogicOperator.And, Parenthesized(rhs));

    private static Formula Definition()
    {
        var q = N("q");
        var alphabet = N("A");
        var a = N("a");
        var b = N("b");
        var x = N("x");
        var y = N("y");
        var index = Call("Fin", q);
        var vertex = Call("Fun", index, alphabet);
        var relation = Seq(x, Colon, vertex, Sp, Mapsto, Sp, y, Colon, vertex, Sp, Mapsto, Sp,
            ExistsIn("a", index, And(Ne(Call("val", x, a), Call("val", y, a)),
                All("b", index, new Formula.Logic(Parenthesized(Ne(b, a)),
                    FormulaLogicOperator.Implies,
                    Parenthesized(Eq(Call("val", x, b), Call("val", y, b))))))));
        return All("q", N("Nat"), All("A", N("Type"), Eq(
            Parenthesized(Seq(Call("coordinateGraph", q, alphabet), Colon, Call("SimpleGraph", vertex))),
            Call("SimpleGraphMk", relation))));
    }

    private static Formula Result()
    {
        var q = N("q");
        var alphabet = N("A");
        var graph = Call("coordinateGraph", q, alphabet);
        var cardinality = Call("card", alphabet);
        var degree = Mul(q, Parenthesized(Call("tsub", cardinality, D(1))));
        return All("q", N("Nat"), All("A", N("Type"), Seq(
            OpenBracket, Call("Fintype", alphabet), CloseBracket,
            And(Call("IsRegularOfDegree", graph, degree),
                Eq(Mul(D(2), Call("edgeCount", graph)),
                    Mul(new Formula.Power(cardinality, q), Parenthesized(degree)))))));
    }
}
