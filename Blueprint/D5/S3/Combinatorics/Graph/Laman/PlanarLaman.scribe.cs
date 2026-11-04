using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Laman;

internal sealed class PlanarLamanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Laman/PlanarLaman.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/chen2026combinatorialrigidity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every finite vertex type in every universe, a simple graph on at least two vertices admits a real planar placement with rigidity kernel dimension at most three exactly when it contains a spanning Laman subgraph.",
        H("Real planar rigidity and spanning Laman graphs"), Blocks(
            Describe.Lean(DescribeId.Create("planar-converse"),
                DeclarationHandle.Create(Prefix + "exists_isLaman_le"),
                H("Independent rows give a spanning Laman subgraph"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every finite enumeration of V, graph G admitting a rigid planar placement, and card(V)>=2, there exists a graph H on the same V with H<=G and H.IsLaman. The ambient graph G may have more edges than H.")),
                    Paragraph(Text("Start with the placement witnessing a kernel of dimension at most three. Openness permits a perturbation along the moment curve for which every vertex subset of size at least three affinely spans the plane. Rank-nullity gives rank at least 2 card(V)-3. Select exactly that many independent actual edge rows and form H from their underlying unordered pairs.")),
                    Paragraph(Text("For every induced subset of H with two vertices, simplicity bounds its edge count by one. On any larger subset, velocity restriction factors its rows through the smaller rigidity map and preserves their independence. Independent translations and a rotation provide three kernel directions there. Rank-nullity gives the induced bound. The selected total edge count is exactly 2 card(V)-3, so H is Laman."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("planar-laman-equivalence"),
                DeclarationHandle.Create(Prefix + "isGenericallyRigid_two_iff_exists_isLaman_le"),
                H("The complete planar equivalence"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Here Framework(V,2) is the space of arbitrary maps from V to the real Euclidean plane. RigidityMap(G,p) sends a velocity x to the edge-indexed inner products of p(u)-p(v) with x(u)-x(v). The kernel and its dimension are over the real numbers. The displayed edge count counts unordered edges, card counts the finite vertex set, and induce(H,S) is the graph induced on S.")),
                    Paragraph(Text("The source predicate IsGenericallyRigid means existence of such a placement. It does not require algebraic independence of coordinates or assert local, global, or rigidity at every placement. The witness in the endpoint has no injectivity premise. Neither G nor H is assumed planar, and the number of vertices has no upper bound.")),
                    Paragraph(Text("The forward implication from a spanning Laman H uses strong induction and the two geometric Henneberg moves to construct a rigid placement of H. The two-vertex case uses K2. Adding the remaining G edges shrinks the kernel. The other implication uses independent edge rows and all induced-subset bounds as above. H has exactly the original vertex type, including any labels; no construction history is an input.")),
                    Paragraph(Text("The Laman predicate combines total tightness with the finite-subset sparsity condition. On finite V, converting a vertex set to its finite set preserves cardinality and the induced edge count. Its eligible-subset condition 3<=2 card(S) is equivalent to card(S)>=2. Thus its two clauses are precisely those displayed, for every induced vertex subset."))),
                DescribeRole.Theorem)), []));

    private static Formula ResultFormula()
    {
        Formula v = F.Id("V"), g = F.Id("G"), h = F.Id("H"), s = F.Id("S"), p = F.Id("p");
        Formula rigid = ExistsIn("p", Call("Framework", v, D(2)),
            Le(Call("finrank", Call("ker", Call("RigidityMap", g, p))), D(3)));
        Formula counts = And(Eq(Add(Call("edgeCount", h), D(3)), Mul(D(2), Call("card", v))),
            All("S", Call("Set", v), Implies(Le(D(2), Call("card", s)),
                Le(Add(Call("edgeCount", Call("induce", h, s)), D(3)),
                    Mul(D(2), Call("card", s))))));
        Formula spanning = ExistsIn("H", Call("SimpleGraph", v), And(Le(h, g), counts));
        return Disp(All("V", F.Id("Type"), Seq(OpenBracket, Call("Finite", v), CloseBracket, Sp,
            All("G", Call("SimpleGraph", v), Implies(Le(D(2), Call("card", v)),
                Logic(rigid, FormulaLogicOperator.Iff, spanning))))));
    }
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), type, body);
    private static Formula ExistsIn(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), op, Seq(Open, b, Close));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
}
