using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Products;

internal sealed class NearEmptyLayerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var v = I("V"); var g = I("G"); var i = I("I");
        var bound = Mul(Sub(C("FintypeCard", v), D(1)), C("indepNum", g));
        var conclusion = Ex("I", C("Finset", C("Prod", v, v)),
            And(C("MaximalIndepSet", C("boxProd", g, g), i), Le(C("card", i), Add(bound, D(1)))));
        var formula = Graph(Imp(C("Connected", g), conclusion));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Deleting a vertex permits a maximum-degree coloring, which limits one row of a maximal independent set to a singleton.",
            H("A nearly empty Cartesian layer"), Blocks(
                Node("NearEmptyLayer", "layer-construction", "The connected nearly-empty-layer bound", "exists_maximalIndepSet_near_empty_layer", formula,
                    "Let G be a finite connected simple graph. Order vertices by decreasing distance from a chosen root, breaking ties injectively. In the graph with that root deleted, each vertex has an original neighbor that is either deleted or later in the order. Greedy coloring therefore uses at most the maximum degree. Assign each color to a different neighbor of a maximum-degree vertex. The resulting independent set dominates its Cartesian row except at the deleted second coordinate. A maximal extension meets that row at most once; every other row contributes at most alpha(G). Maximal means inclusion-maximal, and every finite connected graph, including the singleton, remains in scope."))));
    }
    private static Formula C(string n, params Formula[] a) => a.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(n))
        : new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. a]);
    private static Formula I(string n) => F.Id(n);
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Ex(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula Inst(string n, Formula a, Formula b) => Seq(OpenBracket, C(n, a), CloseBracket, Sp, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Graph(Formula b, bool nonempty = false, bool decidable = false)
    {
        if (decidable) b = Inst("DecidableRel", C("Adj", I("G")), b);
        b = All("G", C("SimpleGraph", I("V")), b);
        if (nonempty) b = Inst("Nonempty", I("V"), b);
        return All("V", C("Type"), Inst("Fintype", I("V"), b));
    }
    private static DocumentBlock Node(string module, string id, string title, string declaration, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Products/" + module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/GraphInvariants/traversogianini2026brooks")),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
