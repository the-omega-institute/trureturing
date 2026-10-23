using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PositionSets;

internal sealed class VertexPositionRatioRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation.";
    private const string Note = "D5/L/GraphInvariants/thankachyetal2024vertexposition";
    private static readonly Formula V = F.Id("V");
    private static readonly Formula G = F.Id("G");
    private static readonly Formula X = F.Id("x");
    private static readonly Formula Y = F.Id("y");
    private static readonly Formula Z = F.Id("z");
    private static readonly Formula S = F.Id("S");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A connected graph family has quadratically many vertices on a sphere from one vertex, "
            + "but only linearly many geodesic rays from another. Its vertex position ratio is unbounded.",
        H("The vertex position ratio is unbounded"),
        Blocks(
            Node("ongeodesic", "Membership in a shortest path", "OnGeodesic", GeodesicFormula(),
                "Definition 2.1, page 3 of arXiv:2209.00359v2, uses the phrase \"lies on any x,y-geodesic in G\". "
                    + "OnGeodesic G x y z means that z belongs to the support of a walk from x to y "
                    + "whose length equals the graph distance. Such a walk is a shortest path; its support "
                    + "includes both endpoints. The predicate expresses existence of one such path.", true),
            Node("isxpositionset", "Position relative to a vertex", "IsXPositionSet", PositionFormula(),
                "Definition 2.1, page 3: \"For any graph G and a fixed vertex x ∈ V(G), a set Sₓ ⊆ V(G) "
                    + "is an x-position set if for any y ∈ Sₓ no vertex of Sₓ \\ {y} lies on any x,y-geodesic in G.\" "
                    + "The finite set S represents Sₓ. For each selected y, every other selected z is excluded "
                    + "from every shortest x,y-path. This includes the endpoint x: a set containing x and another "
                    + "vertex fails the condition in a connected graph. The singleton {x} is permitted.", true),
            Node("posnum", "The x-position number", "posNum", PosNumFormula(),
                "Definition 2.1, page 3: \"The x-position number of G is defined to be the maximum cardinality "
                    + "of an x-position set and is denoted by pₓ(G) or simply pₓ.\" The finite supremum ranges "
                    + "over all finite subsets of V satisfying IsXPositionSet G x, including the empty set. "
                    + "Finset.card counts vertices once; the full finite carrier, not a chosen candidate list, is used.", true),
            Node("vp", "The upper vertex position number", "vp", VpFormula(false),
                "Definition 2.1, page 3: \"The maximum value of pₓ(G) among all vertices x of G is called "
                    + "the upper vertex position number vp(G) (or simply the vertex position number) of G.\" "
                    + "vp takes the supremum of posNum over the entire finite vertex carrier.", true),
            Node("vpminus", "The minimum vertex position number", "vpMinus", VpFormula(true),
                "Definition 2.1, pages 3–4: \"Similarly, the minimum value of pₓ(G) among all vertices of G "
                    + "is called the minimum vertex position number vp⁻(G) of G.\" Nonempty V ensures that "
                    + "Finset.univ is nonempty. The proof argument of inf' is suppressed in the formula; "
                    + "it is Finset's proof that the universal finite set is nonempty. Every vertex is included.", true),
            Node("claim", "Problem 2.4: boundedness on connected graphs", "claim", ClaimFormula(),
                "Problem 2.4, page 5: \"Is the ratio vp(G)/vp⁻(G) bounded for connected graphs?\" "
                    + "The question is encoded as one real constant C valid for every finite nonempty vertex "
                    + "carrier and every connected simple graph on it, with decidable adjacency. The numbers "
                    + "are coerced from naturals to reals. A singleton is an x-position set, so vpMinus is positive "
                    + "on these carriers; multiplication by it faithfully expresses ratio boundedness. "
                    + "No bound on graph order or restriction to a subclass is imposed.", true),
            Node("result", "A family refutes the proposed boundedness", "result", Seq(Neg, Sp, Call("claim")),
                "For each integer m ≥ 2, take one hub y and 2m+1 paths meeting only at y: "
                    + "H of length 4m, m paths Pᵢ of length 4m, and m paths Qⱼ of length aⱼ = 2m+2j "
                    + "for 1 ≤ j ≤ m. Add H at level bⱼ to Qⱼ at the same level, where bⱼ = 2m+j+1; "
                    + "join the tip Qⱼ at level aⱼ to every Pᵢ at that level. An edge changes its level by "
                    + "at most one, so every ray is shortest from y. A y-position set meets each ray in at most "
                    + "one vertex, giving posNum at y at most 2m+1. At x = H at level 4m, a second potential "
                    + "changes by at most one along every edge. Together with explicit walks, it puts all "
                    + "m(m−1) vertices Pᵢ at levels aⱼ+1, for j < m, at distance 2m+1 from x. "
                    + "A sphere is an x-position set: any different selected vertex inside a shortest path "
                    + "would have smaller distance from x. Consequently vp is at least m(m−1) and vpMinus "
                    + "is at most 2m+1. The quadratic lower bound exceeds C(2m+1) for some m for each "
                    + "real C. This contradicts claim. The lower bound, rather than an exact value of either "
                    + "invariant on the family, suffices. The source's separate degree, eccentricity and "
                    + "graph-class results are not assertions of boundedness and retain their stated scopes.", false,
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("thankachy-et-al-2024-vertex-position-ratio"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, bool literature, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note))
                : AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolution);

    private static Formula GeodesicFormula()
    {
        var p = F.Id("p");
        return All(V, Named("Type"), All(G, Call("SimpleGraph", V),
            All(X, V, All(Y, V, All(Z, V,
                IffFormula(Call("OnGeodesic", G, X, Y, Z),
                    ExistsFormula(p, App(Field(G, "Walk"), X, Y),
                        AndFormula(Rel(Field(p, "length"), Eq, App(Field(G, "dist"), X, Y)),
                            Rel(Z, InMacro, Field(p, "support"))))))))));
    }

    private static Formula PositionFormula() => All(V, Named("Type"), All(G, Call("SimpleGraph", V),
        All(X, V, All(S, Call("Finset", V),
            IffFormula(Call("IsXPositionSet", G, X, S),
                All(Y, V, ImpliesFormula(Rel(Y, InMacro, S), All(Z, V,
                    ImpliesFormula(Rel(Z, InMacro, S),
                        ImpliesFormula(new Formula.Relation(Z, FormulaRelationOperator.NotEqual, Y), Seq(Neg, Sp,
                            Parenthesized(Call("OnGeodesic", G, X, Y, Z)))))))))))));

    private static Formula PosNumFormula()
    {
        var allSets = Parenthesized(Seq(Qualified("Finset", "univ"), Colon,
            Call("Finset", Call("Finset", V))));
        var filtered = App(Field(allSets, "filter"), Call("IsXPositionSet", G, X));
        return FiniteCarrier(All(G, Call("SimpleGraph", V), All(X, V,
            Rel(Call("posNum", G, X), Eq, App(Field(Parenthesized(filtered), "sup"),
                Qualified("Finset", "card"))))), false);
    }

    private static Formula VpFormula(bool minimum)
    {
        var allVertices = Parenthesized(Seq(Qualified("Finset", "univ"), Colon, Call("Finset", V)));
        var operation = minimum ? Seq(Field(allVertices, "inf"), Apos) : Field(allVertices, "sup");
        return FiniteCarrier(All(G, Call("SimpleGraph", V),
            Rel(Call(minimum ? "vpMinus" : "vp", G), Eq, App(operation, Call("posNum", G)))), minimum);
    }

    private static Formula ClaimFormula()
    {
        var c = F.Id("C");
        var realVp = Parenthesized(Seq(Call("vp", G), Colon, Reals));
        var realMin = Parenthesized(Seq(Call("vpMinus", G), Colon, Reals));
        return IffFormula(Call("claim"), ExistsFormula(c, Reals,
            FiniteCarrier(All(G, Call("SimpleGraph", V),
                Instance(Call("DecidableRel", Field(G, "Adj")),
                    ImpliesFormula(Field(G, "Connected"),
                        Rel(realVp, Le, Seq(c, Sp, Cdot, Sp, realMin))))), true)));
    }

    private static Formula Reals => Seq(Mathbb, Sp, F.Id("R"));
    private static Formula FiniteCarrier(Formula body, bool nonempty) => All(V, Named("Type"),
        Instance(Call("Fintype", V), Instance(Call("DecidableEq", V),
            nonempty ? Instance(Call("Nonempty", V), body) : body)));
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Field(Formula value, string name) => Seq(value, Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula App(Formula function, params Formula[] args) =>
        args.Length == 0 ? function : Seq(function, Parenthesized(Join(args)));
    private static Formula Join(Formula[] args) => Seq(args.SelectMany(
        (arg, index) => index == 0 ? new[] { arg } : new[] { Comma, Sp, arg }).ToArray());
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(variable, Colon, type)), Comma, Sp, body);
    private static Formula ExistsFormula(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(variable, Colon, type)), Comma, Sp, body);
    private static Formula Rel(Formula a, Formula relation, Formula b) => Seq(a, Sp, relation, Sp, b);
    private static Formula IffFormula(Formula a, Formula b) =>
        Rel(Parenthesized(a), Iff, Parenthesized(b));
    private static Formula AndFormula(Formula a, Formula b) =>
        Rel(Parenthesized(a), Land, Parenthesized(b));
    private static Formula ImpliesFormula(Formula a, Formula b) =>
        Rel(Parenthesized(a), Longrightarrow, Parenthesized(b));
}
