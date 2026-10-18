using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Products;

internal sealed class EmptyLayerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var v = I("V"); var g = I("G"); var i = I("I");
        var bound = Mul(Sub(C("FintypeCard", v), D(1)), C("indepNum", g));
        var conclusion = Ex("I", C("Finset", C("Prod", v, v)),
            And(C("MaximalIndepSet", C("boxProd", g, g), i), Le(C("card", i), bound)));
        var formula = Graph(Imp(Le(C("chromaticNumber", g), C("maxDegree", g)), conclusion), true, true);
        return DocumentDefinition.Create(ScribeNode.Create(
            "A coloring with at most the maximum degree permits a maximal independent set to omit an entire Cartesian layer.",
            H("An empty Cartesian layer"), Blocks(
                Node("EmptyLayer", "layer-construction", "The chromatic empty-layer bound", "exists_maximalIndepSet_empty_layer", formula,
                    "Let G be any finite nonempty simple graph with chromatic number at most maximum degree. Choose a proper coloring with that many colors and inject the colors into the neighbors of a maximum-degree vertex v. The pairs (neighbor(color(y)),y) form an independent set that dominates the entire row with first coordinate v. Extend this prescribed set to an inclusion-maximal independent set. It avoids that row, so the other |V|-1 rows contribute at most (|V|-1) alpha(G). No regularity or connectedness hypothesis is imposed."))));
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
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
