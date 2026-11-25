using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal.Reconstruction;

internal sealed class WeightedTwoStepBFSDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every weighted two-step breadth-first potential has residual at most four for defect-one gains.",
        H("The weighted two-step breadth-first potential"),
        Blocks(Describe.Lean(
            DescribeId.Create("two-step-residual-bound"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Chordal/Reconstruction/WeightedTwoStepBFS.two_step_residual_bound"),
            H("A uniform bound for arbitrary predecessor weights"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Flat means skew with absolute triangle defect at most one. Anchor choices use the root at depth one and a common predecessor of the shadow in the parent shadow at each later depth. The weights are nonnegative, vanish off the predecessor set, and sum to one at each nonroot vertex.")),
                Paragraph(Text("The potential P transports along successive anchors and adds the weighted mean of the two-edge paths through the predecessors. Root edges have zero residual. Within one layer, both endpoints have the same anchor. The shadow is a clique, and a diagonal in the four-cycle formed by the endpoints and their predecessors yields a comparison using at most three triangles. Across consecutive layers the common transport cancels and four triangle comparisons suffice. Averaging over the predecessor pair preserves the bound."))),
            DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula For(string n, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
    private static Formula If(Formula p, Formula q) =>
        new Formula.Logic(Seq(Open, p, Close), FormulaLogicOperator.Implies, Seq(Open, q, Close));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);

    private static Formula Statement()
    {
        var V = F.Id("V"); var G = F.Id("G"); var r = F.Id("r"); var g = F.Id("g");
        var a = F.Id("a"); var w = F.Id("w"); var u = F.Id("u"); var v = F.Id("v");
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var tables = Arrow(V, Arrow(V, real));
        Formula value(Formula x) => Apply("P", G, r, a, w, g, x);
        var error = Seq(Lvert, Sp, Apply("eval", g, u, v), Minus,
            Open, value(v), Minus, value(u), Close, Rvert, Sp);
        var edge = For("u", V, For("v", V, If(Apply("Adj", G, u, v),
            new Formula.Relation(error, FormulaRelationOperator.LessThanOrEqual, D(4)))));
        var laws = If(Apply("Anchors", G, r, a),
            If(Apply("Weights", G, r, w), If(Apply("Flat", G, g), edge)));
        var choices = For("r", V, For("a", Apply("AnchorFamily", G, r),
            For("w", tables, For("g", tables, laws))));
        var graph = For("G", Apply("SimpleGraph", V),
            If(Apply("Chordal", G), If(Apply("Connected", G), choices)));
        return For("level", Apply("Universe"), For("V", Apply("Type", F.Id("level")),
            Seq(OpenBracket, Apply("Fintype", V), CloseBracket, Comma, Sp, graph)));
    }
}
