using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class GuerreroVertexEnergyDegreeBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/GuerreroVertexEnergyDegreeBounds.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/guerrero2022laplacianenergies");

    public DocumentDefinition Create()
    {
        Formula v = V("V"), g = V("G"), i = V("v"), m = V("M"), x = V("x");
        Formula absolute = Carrier(All("M", Call("Matrix", v, v, C("Real")),
            Eqn(Call("matAbs", m), Call("cfc",
                Parenthesized(Seq(LambdaLower, Sp, x, Colon, Sp, C("Real"), Sp, Mapsto, Sp,
                    new Formula.Absolute(x))), m))));
        Formula energy = Graph(All("v", v, Eqn(Call("vertexEnergy", g, i),
            App(Call("matAbs", Adj(g)), i, i))));
        Formula inverse = Graph(Eqn(Call("degInvSqrt", g),
            App(Q("Matrix", "diagonal"), Parenthesized(Seq(LambdaLower, Sp, i, Colon, Sp, v,
                Sp, Mapsto, Sp, new Formula.Fraction(D(1),
                    App(Q("Real", "sqrt"), Cast(App(Q("SimpleGraph", "degree"), g, i)))))))));
        Formula laplacian = Graph(Eqn(Call("normLap", g),
            Sub(D(1), Mul(Mul(Call("degInvSqrt", g), Adj(g)), Call("degInvSqrt", g)))));
        Formula normalizedEnergy = Graph(All("v", v, Eqn(Call("normLapVertexEnergy", g, i),
            App(Call("matAbs", Parenthesized(Sub(Call("normLap", g), D(1)))), i, i))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "A six-vertex path disproves the upper local comparison between adjacency and normalized Laplacian energies.",
            H("Vertex energies and the maximum-degree bound"), Blocks(
                Node("absolute", "Absolute value of a real symmetric matrix", "matAbs", absolute,
                    "Page 2 uses |A| in the sentence: \"Given a vertex v_i ∈ V, its energy is defined as E_G(v_i) := |A|_ii.\" For a real symmetric matrix, cfc (fun x : ℝ => |x|) is its spectral absolute value: an orthonormal eigenbasis replaces every eigenvalue by its absolute value. The formula gives this expression on finite real matrices.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("energy", "Adjacency energy of a vertex", "vertexEnergy", energy,
                    "Page 2: \"Given a vertex v_i ∈ V, its energy is defined as E_G(v_i) := |A|_ii.\" The matrix A is SimpleGraph.adjMatrix G ℝ, and v is the diagonal index. Every finite vertex type and its adjacency decision procedure are quantified.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("inverse", "Inverse square root of the degree matrix", "degInvSqrt", inverse,
                    "Page 1: \"L := I − D^{−1/2} A D^{−1/2}, where D is the diagonal degree matrix, D_ii = d_i.\" The displayed diagonal has entry 1 / √d_v, with the natural degree coerced to ℝ. Real division assigns zero to the reciprocal of zero; the counterexample has positive degree at every vertex.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("laplacian", "Normalized Laplacian", "normLap", laplacian,
                    "Page 1: \"L := I − D^{−1/2} A D^{−1/2}, where D is the diagonal degree matrix, D_ii = d_i.\" The identity and products are real matrix operations, with D^{−1/2} given by degInvSqrt.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("normalized", "Normalized Laplacian energy of a vertex", "normLapVertexEnergy", normalizedEnergy,
                    "Section 4, page 9: \"For a connected simple graph G = (V, E) we define the normalized Laplacian energy of a vertex v_i ∈ V as LE_G(v_i) := φ_i(|L − I|)\". Here φ_i(M) = M_ii, so the expression is the corresponding diagonal of matAbs (normLap G − 1).",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("claim", "Remark 6 (Conjecture)", "claim", Eqn(Call("claim"), Parenthesized(ClaimBody())),
                    "Remark 6 (Conjecture), page 13: \"In Theorem 17 of [6] it is proven that d_min LE(G) ≤ E(G) ≤ d_max LE(G), where d_min and d_max are the minimum and maximum degrees of G respectively. According to numerical experiments the analog result is true for the energy of vertices, that is: d_min LE_G(v) ≤ E_G(v) ≤ d_max LE_G(v) for all v ∈ V.\" Page 1 states: \"We will assume that G is simple and connected.\" The proposition quantifies both inequalities over every vertex of every finite simple connected graph, using minDegree and maxDegree coerced to ℝ.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("result", "Refutation on the six-vertex path", "result", Seq(Neg, Sp, Parenthesized(ClaimBody())),
                    "At zero-based vertex 2 of SimpleGraph.pathGraph 6 the adjacency energy is (7 + 4b − 2b²)/7, where 1 < b < 4/3 and b³ + b² − 2b − 1 = 0. Positive semidefinite square-root certificates identify this value and the normalized Laplacian energy (4 + √5)/10. The adjacency energy exceeds 5/4, whereas twice the normalized energy is below 5/4. The maximum degree is two. Thus the upper inequality fails. This proves no universal assertion about the lower inequality or about blow-ups. Literature completeness is ASSUMED-UNVERIFIED: the statement compared here is arXiv v1; the publisher edition and an exhaustive search of citing works have not been verified.",
                    DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                    new OpenProblemResolutionClaim(
                        ProblemSlugRef.Create("guerrero-2022-vertex-energy-degree-bounds-remark-6"),
                        ResolutionKind.Refuted)))));
    }

    private static Formula ClaimBody()
    {
        Formula g = V("G"), v = V("v");
        return Graph(Imp(App(Q("SimpleGraph", "Connected"), g), Parenthesized(All("v", V("V"),
            new Formula.Logic(Le(Mul(Cast(App(Q("SimpleGraph", "minDegree"), g)),
                    Call("normLapVertexEnergy", g, v)), Call("vertexEnergy", g, v)),
                FormulaLogicOperator.And,
                Le(Call("vertexEnergy", g, v), Mul(Cast(App(Q("SimpleGraph", "maxDegree"), g)),
                    Call("normLapVertexEnergy", g, v))))))));
    }

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("guerrero-energy-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula Carrier(Formula body) => All("V", C("Type"), Seq(
        OpenBracket, Call("Fintype", V("V")), CloseBracket, Sp,
        OpenBracket, Call("DecidableEq", V("V")), CloseBracket, Sp, body));
    private static Formula Graph(Formula body) => Carrier(All("G", Call("SimpleGraph", V("V")), Seq(
        OpenBracket, Call("DecidableRel", App(Q("SimpleGraph", "Adj"), V("G"))), CloseBracket, Sp, body)));
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Q(string owner, string name) => Seq(C(owner), Dot, C(name));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? C(name) : App(C(name), args);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Adj(Formula graph) => App(Q("SimpleGraph", "adjMatrix"), graph, C("Real"));
    private static Formula Cast(Formula value) => Parenthesized(Seq(value, Colon, Sp, C("Real")));
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
