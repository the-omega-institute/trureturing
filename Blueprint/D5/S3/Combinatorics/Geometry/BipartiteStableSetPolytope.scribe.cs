using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class BipartiteStableSetPolytopeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/BipartiteStableSetPolytope.";
    private static Formula V => F.Id("V");
    private static Formula G => F.Id("G");
    private static Formula Real => F.Id("Real");
    private static Formula Vector => Seq(V, To, Real);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bipartite graphs are exactly the finite graphs whose independent-set hull is described by bounds and edge inequalities.",
        H("Independent-set polytopes on the original vertex labels"),
        Blocks(
            Paragraph(Text("Let V be any universe-polymorphic vertex type and G a native simple graph on V. All vectors are functions V to the reals. The finite-type hypothesis appears only in the characterization; no inhabitance, connectedness, edge, enumeration or rational-coordinate assumption is imposed.")),
            Node("vertexIndicator", "Finite-set indicators", DescribeRole.Definition,
                All("V", F.Id("Type"), All("A", Call("Finset", V),
                    Equal(Call("vertexIndicator", F.Id("A")),
                        Call("indicator", Call("Set", F.Id("A")), Call("constant", D(1)))))),
                "vertexIndicator(A) is the native Set.indicator of the underlying set of A, with value one on A and zero elsewhere. It retains every original label, including isolated vertices."),
            Node("stableSetPolytope", "The actual independent-set hull", DescribeRole.Definition,
                All("V", F.Id("Type"), All("G", Call("SimpleGraph", V),
                    Equal(Call("stableSetPolytope", G), Call("convexHull", Real,
                        Seq(OpenBrace, Call("vertexIndicator", F.Id("A")), Sp, Bar, Sp,
                            F.Id("A"), Colon, Call("Finset", V), Comma, Sp,
                            Call("IsIndepSet", G, Call("Set", F.Id("A"))), CloseBrace))))),
                "Take the real convex hull of the range of vertexIndicator on the subtype of independent Finsets. Independence is the native graph predicate on the underlying set. This is a set of actual real vectors on V."),
            Node("edgeRegion", "Bounds and edge inequalities", DescribeRole.Definition,
                All("V", F.Id("Type"), All("G", Call("SimpleGraph", V),
                    All("x", Vector, Iff(Member(F.Id("x"), Call("edgeRegion", G)),
                        And(All("v", V, And(Le(D(0), Call("x", F.Id("v"))),
                                Le(Call("x", F.Id("v")), D(1)))),
                            All("v", V, All("w", V,
                                Imp(Call("Adj", G, F.Id("v"), F.Id("w")),
                                    Le(Seq(Call("x", F.Id("v")), Plus, Call("x", F.Id("w"))), D(1)))))))))),
                "Every coordinate lies between zero and one. Every adjacent pair has coordinate sum at most one. Upper bounds at isolated vertices are part of the definition."),
            Node("stableSetPolytope_eq_edgeRegion_iff", "The bipartite characterization", DescribeRole.Theorem,
                All("V", F.Id("Type"), Seq(OpenBracket, Call("Finite", V), CloseBracket, Sp,
                    All("G", Call("SimpleGraph", V), Iff(
                        Equal(Call("stableSetPolytope", G), Call("edgeRegion", G)),
                        Call("IsBipartite", G))))),
                "For every finite V and every simple graph G on V, equality of these two sets of real vectors is equivalent to native bipartiteness. The statement includes empty vertex types, isolated vertices and disconnected graphs."),
            Paragraph(Text("Every independent indicator satisfies the inequalities, and the inequality region is convex. For the converse inclusion under bipartiteness, fix a total two-coloring and complement the coordinates in one color. The transformed vector lies in the unit cube and increases along edges oriented from the first color to the second. Its positive support defines an independent indicator after the complement is undone. Peel off the minimum positive level delta. If delta equals one, the vector is already that indicator. Otherwise subtract delta on the positive support and divide by one minus delta; the new positive support is strictly smaller. Induction reconstructs a convex combination on the same V. On the complemented color the reconstruction uses delta times (one minus the support indicator), plus one minus delta times (one minus the residual coordinate). Thus isolated labels and tied minimum levels are retained.")),
            Paragraph(Text("For necessity, the constant one-half vector belongs to the inequality region. A finite convex representation in independent indicators has a positive coefficient. Fix one such coefficient before considering any edge. Equality in the weighted edge bound forces that same indicator to meet every edge in exactly one endpoint. Its underlying set and complement form a bipartition. Selection uses the convex-combination index type, so it also applies when V is empty. The construction establishes the classical graph-polyhedral characterization; no claim of mathematical originality is made.")))));

    private static DocumentBlock Node(string name, string title, DescribeRole role, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("bipartite-polytope-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula Call(string name, params Formula[] arguments) => Seq(F.Id(name), Open,
        Seq(arguments.SelectMany((value, index) => index == 0 ? new[] { value } : new[] { Comma, Sp, value }).ToArray()), Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
