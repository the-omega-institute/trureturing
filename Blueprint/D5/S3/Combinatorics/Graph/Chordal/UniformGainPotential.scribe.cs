using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal;

internal sealed class UniformGainPotentialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Triangle defects give an edge error bound independent of the number of vertices.",
        H("Uniform approximation of chordal group gains"),
        Blocks(
            Paragraph(Text("Let V be a finite vertex type and H a group with a pseudometric invariant under both left and right multiplication. An oriented edge from i to j carries a label g(i,j). Reversing an edge inverts its label exactly. For each ordered triangle, the distance between g(i,j)g(j,k) and g(i,k) is at most a common nonnegative real number epsilon.")),
            Describe.Lean(
                DescribeId.Create("uniform-chordal-gain-potential"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Chordal/UniformGainPotential.SimpleGraph.IsChordal.exists_uniform_approximate_gain_potential"),
                H("A uniform four-defect bound"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The two isometric actions express invariance under left and right multiplication. One potential phi gives the claimed error on every oriented edge, with a coefficient independent of the number of vertices.")),
                    Paragraph(Text("Choose a root in each connected component and assign vertices their distance from the root. For a component of the subgraph at or above a given layer, its shadow consists of its neighbors in the preceding layer. Two nonadjacent shadow vertices would admit shortest paths through that component and through lower layers. The interiors of these paths are disjoint and have no edges between them. Their union would therefore be a chordless cycle of length at least four.")),
                    Paragraph(Text("For every shadow above the root, each vertex in it has a predecessor in the parent shadow. The predecessor sets are linearly ordered by inclusion, since two incomparable sets give a chordless four-cycle. A member of a smallest predecessor set is adjacent to the whole shadow. Use this member as the component anchor, with the root as anchor in the first layer.")),
                    Paragraph(Text("Transport along the chain of anchors. To reach a vertex from its component anchor, pass through a chosen predecessor. A cross-layer edge requires at most two triangle comparisons on each side of its shared shadow. For an edge within a layer, the two predecessors coincide or lie in a four-cycle whose chord yields a comparison using at most three triangles. Reversing an edge preserves its error by inversion.")),
                    Paragraph(Text("The construction treats each connected component separately and applies to an empty graph. When epsilon is zero, every edge has zero error in the given pseudometric."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(P(a), FormulaLogicOperator.Implies, P(b));
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);

    private static Formula Statement()
    {
        var v = F.Id("V");
        var h = F.Id("H");
        var graph = F.Id("G");
        var i = F.Id("i");
        var j = F.Id("j");
        var k = F.Id("k");
        var eps = F.Id("epsilon");
        Formula adj(Formula a, Formula b) => Call("Adj", graph, a, b);
        Formula gain(Formula a, Formula b) => Call("g", a, b);
        Formula pot(Formula a) => Call("phi", a);
        var reversal = All("i", v, All("j", v,
            Imp(adj(i, j), Eqn(gain(j, i), Call("inv", gain(i, j))))));
        var triangle = All("i", v, All("j", v, All("k", v,
            Imp(adj(i, j), Imp(adj(j, k), Imp(adj(i, k),
                Le(Call("dist", Mul(gain(i, j), gain(j, k)), gain(i, k)), eps)))))));
        Formula result = Some("phi", new Formula.TypeArrow(v, h),
            All("i", v, All("j", v, Imp(adj(i, j),
                Le(Call("dist", gain(i, j), Mul(Call("inv", pot(i)), pot(j))),
                    Mul(D(4), eps))))));
        result = Imp(reversal, Imp(triangle, result));
        result = All("epsilon", Call("Real"), Imp(Le(D(0), eps), result));
        result = All("g", new Formula.TypeArrow(v, new Formula.TypeArrow(v, h)), result);
        result = All("G", Call("SimpleGraph", v), Imp(Call("IsChordal", graph), result));
        result = Seq(
            OpenBracket, Call("Finite", v), CloseBracket, Sp,
            OpenBracket, Call("Group", h), CloseBracket, Sp,
            OpenBracket, Call("PseudoMetricSpace", h), CloseBracket, Sp,
            OpenBracket, Call("IsIsometricSMul", h, h), CloseBracket, Sp,
            OpenBracket, Call("IsIsometricSMul", Call("MulOpposite", h), h),
                CloseBracket, Comma, Sp, result);
        result = All("V", Call("Type", F.Id("u")), All("H", Call("Type", F.Id("v")), result));
        return All("u", Call("Universe"), All("v", Call("Universe"), result));
    }
}
