using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal;

internal sealed class TwoTreeFamilyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/Chordal/TwoTreeFamily.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed edge balances determine the triangle coordinates of a circulation.",
        H("Circulations of recursive two-trees"),
        Blocks(
            Paragraph(Text("Orient the core triangle cyclically. Each inserted vertex lies between the source and target of its parent edge. Orient the two new edges along that path and retain the old orientation on the parent.")),
            Entry("two-tree-triangle-coordinate", "twoTree_triangle_chain_coordinate",
                "Coordinates of triangle chains", Coordinate(),
                "At each fresh vertex, conservation makes the two child coefficients equal. Subtracting that coefficient times the insertion triangle clears the two children and adds the coefficient to their parent edge. This reduces to a circulation on the preceding round. On the core, the three coefficients are equal. The reverse construction is linear and restores the original circulation."),
            Entry("two-tree-triangles-classify", "twoTree_triangles_classify",
                "Triangles of the graph", Classification(),
                "A triangle either lies in the preceding graph or contains a single newest vertex and its two parents."),
            Entry("two-tree-filling-norm", "twoTree_filling_norm_eq",
                "Triangle-filling norm", Filling(),
                "The triangle chains are an integral basis and remain a basis with real coefficients. Every filling has the same coefficient vector, so its length is the sum of the absolute values of those coordinates."),
            Entry("two-tree-gain-pairing", "twoTree_triangle_gain_pairing",
                "Evaluation of triangle gains", Pairing(),
                "Give the first child zero gain and give the second child the parent gain plus the prescribed triangle value. Evaluating on a circulation cancels the parent contribution introduced when the newest triangle is removed."))));

    private static DocumentBlock Entry(string id, string name, string title, Formula statement,
        string proof) => Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + name),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(proof))), DescribeRole.Theorem);

    private static Formula I(string name) => F.Id(name);
    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(I(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(P(a), FormulaLogicOperator.Implies, P(b));
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(P(a), FormulaLogicOperator.And, P(b));
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Instance(Formula type) => Seq(OpenBracket, type, CloseBracket, Sp);
    private static Formula Depth(Formula body) => All("d", Call("Nat"), body);
    private static Formula Triangles => Call("TwoTreeTriangles", I("d"));
    private static Formula Vertices => Call("TwoTreeV", I("d"));
    private static Formula Circulation(Formula ring) => Call("TwoTreeCirculation", ring, I("d"));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(I(name), Sp, Colon, Sp, type)), Sp, P(body));

    private static Formula Coordinate()
    {
        var r = I("R");
        var d = I("d");
        var i = I("i");
        return All("ell", Call("Universe"), All("R", Call("Type", I("ell")),
            Seq(Instance(Call("CommRing", r)), Comma, Sp,
                Depth(All("i", Triangles, Eqn(
                    Call("twoTreeCirculationCoordinates", r, d, Call("twoTreeTriangleChain", r, d, i)),
                    Call("single", i, D(1))))))));
    }

    private static Formula Classification()
    {
        var d = I("d");
        var a = I("a");
        var b = I("b");
        var c = I("c");
        Formula adj(Formula x, Formula y) => Call("Adj", Call("twoTree", d), x, y);
        var body = Some("i", Triangles,
            Eqn(Call("twoTreeTriangleVertices", d, I("i")), new Formula.SetLiteral([a, b, c])));
        var allTriangles = All("a", Vertices, All("b", Vertices, All("c", Vertices,
            Imp(adj(a, b), Imp(adj(b, c), Imp(adj(a, c), body))))));
        var i = I("i");
        var triple = Call("twoTreeOrientedTriangle", d, i);
        var first = Call("fst", triple);
        var second = Call("fst", Call("snd", triple));
        var third = Call("snd", Call("snd", triple));
        var validTriangles = All("i", Triangles,
            And(adj(first, second), And(adj(second, third), adj(third, first))));
        return Depth(And(allTriangles, validTriangles));
    }

    private static Formula Filling()
    {
        var r = Call("Real");
        var d = I("d");
        var z = I("z");
        return Depth(All("z", Circulation(r), Eqn(Call("twoTreeFillingNorm", d, z),
            Call("norm", Call("toLp", D(1), Call("twoTreeCirculationCoordinates", r, d, z))))));
    }

    private static Formula Pairing()
    {
        var r = I("R");
        var e = I("E");
        var d = I("d");
        var z = I("z");
        var i = I("i");
        var j = I("j");
        var tau = I("tau");
        var edgeGain = Call("twoTreeTriangleGain", d, tau,
            Call("twoTreeEdgeSource", d, j), Call("twoTreeEdgeTarget", d, j));
        var left = SumOver("j", Call("TwoTreeEdges", d), Call("smul", Call("val", z, j), edgeGain));
        var right = SumOver("i", Triangles, Call("smul",
            Call("twoTreeCirculationCoordinates", r, d, z, i), Call("tau", i)));
        var body = Depth(All("tau", new Formula.TypeArrow(Triangles, e),
            All("z", Circulation(r), Eqn(left, right))));
        return All("ell", Call("Universe"), All("vee", Call("Universe"),
            All("R", Call("Type", I("ell")), All("E", Call("Type", I("vee")),
                Seq(Instance(Call("CommRing", r)), Instance(Call("AddCommGroup", e)),
                    Instance(Call("Module", r, e)), Comma, Sp, body)))));
    }
}
