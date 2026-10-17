using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.GeneralPosition;

internal sealed class CylinderSevenTenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/klavzaretal2026mobileproducts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The mobile general position number of the seven-cycle and ten-cycle cylinders is four at every height at least five.",
        H("Mobile general position on two exceptional cylinders"),
        Blocks(
            Paragraph(Text("Vertices are pairs in Fin r × Fin s. The cycle coordinate is numbered from zero modulo r, and the path coordinate is numbered from zero to s−1. Finite sets record occupied vertices, with one robot at each vertex. Distances are SimpleGraph.dist. The cylinders in the theorem are finite and connected.")),
            Node("geodesic", "A vertex between two others", "OnGeodesic", DescribeRole.Definition,
                GraphParameters(All("u", X("V"), All("v", X("V"), All("w", X("V"),
                    Eq(Call("OnGeodesic", X("G"), X("u"), X("v"), X("w")),
                        Eq(Add(Dist("u", "v"), Dist("v", "w")), Dist("u", "w")))))), false),
                AssessedProvenance.FromLiterature(Source),
                "Section 1.1, PDF page 3: “The distance between vertices u, v ∈ V(G) is the length of a shortest u, v-path in G.” On these connected graphs, equality of the two distances through v with the endpoint distance says that v lies on a shortest path from u to w."),
            Node("general-position", "General position", "IsGeneralPosition", DescribeRole.Definition,
                GraphParameters(All("S", Call("Finset", X("V")),
                    Eq(Call("IsGeneralPosition", X("G"), X("S")), Parenthesized(GeneralPositionBody()))), false),
                AssessedProvenance.FromLiterature(Source),
                "Section 1.1, PDF page 3: “If S ⊆ V(G) has the property that no three vertices of S lie on a common shortest path of G, then we say that S is a general position set of G.” The three vertices are pairwise distinct, and each belongs to the occupied finite set."),
            Node("legal-move", "One legal robot move", "LegalMove", DescribeRole.Definition,
                GraphParameters(All("S", Call("Finset", X("V")), All("T", Call("Finset", X("V")),
                    Eq(Call("LegalMove", X("G"), X("S"), X("T")), Parenthesized(LegalMoveBody()))))),
                AssessedProvenance.FromLiterature(Source),
                "Section 1.1, PDF pages 3–4: “If a robot is located at a vertex u and u ∼ v, then we indicate the movement of the robot from u to v along the edge uv by u ⇝ v and refer to this as a move.” “If a robot is stationed at a vertex u of S, then the move u ⇝ v is called a legal move if i) v ∉ S (thereby avoiding having more than one robot per vertex at any stage) and ii) the new set (S ∖ {u}) ∪ {v} is also a general position set.” The target is insert v (S.erase u)."),
            Node("mobility", "A finite traversal of the graph", "IsMobile", DescribeRole.Definition,
                GraphParameters(All("S", Call("Finset", X("V")),
                    Eq(Call("IsMobile", X("G"), X("S")), MobileBody()))),
                AssessedProvenance.FromLiterature(Source),
                "Section 1.1, PDF page 4: “A configuration of robots on a general position set of G is called a mobile general position set if there is a sequence of legal moves starting from S such that every vertex of G is visited at least once by some robot.” A sequence has n+1 configurations indexed by Fin (n+1); each consecutive pair is a legal move, and their union contains every vertex."),
            Node("number", "The mobile general position number", "mobGP", DescribeRole.Definition,
                GraphParameters(Eq(Call("mobGP", X("G")), Call("sSup",
                    Seq(OpenBrace, X("k"), Sp, Colon, Sp, Nat(), Sp, Mid, Sp,
                        Ex("S", Call("Finset", X("V")),
                            And(Eq(QCall("Finset", "card", X("S")), X("k")), Call("IsMobile", X("G"), X("S")))),
                        CloseBrace)))),
                AssessedProvenance.FromLiterature(Source),
                "Section 1.1, PDF page 4: “The mobile general position number, written Mobgp(G), is the largest number of robots in a mobile general position set of G.” The natural-number supremum is taken over the cardinalities of finite mobile sets; for the finite cylinders it is attained and bounded by the vertex count."),
            Node("cylinder", "The Cartesian product graph", "cylinder", DescribeRole.Definition,
                All("r", Nat(), All("s", Nat(), Eq(Call("cylinder", X("r"), X("s")),
                    QCall("SimpleGraph", "boxProd", Call("cycleGraph", X("r")), Call("pathGraph", X("s")))))),
                AssessedProvenance.FromLiterature(Source),
                "Section 2, PDF page 4: “Recall that the Cartesian product G □ H of graphs G and H satisfies V(G □ H) = V(G) × V(H) and (g, h)(g′, h′) ∈ E(G □ H) if either gg′ ∈ E(G) and h = h′, or g = g′ and hh′ ∈ E(H).” Here the factors are cycleGraph r and pathGraph s."),
            Node("claim", "The two remaining cylinder cases", "claim", DescribeRole.Definition,
                Eq(X("claim"), Parenthesized(ClaimBody())), AssessedProvenance.FromLiterature(Source),
                "Section 3, PDF page 15, after Proposition 3.7: “Hence, the only unknown values are Mobgp(C₇ □ Pₛ) and Mobgp(C₁₀ □ Pₛ) for s ≥ 5. We conjecture that the answer is four in these cases.” The parameter s counts the vertices of the path. Both asserted values are four for every natural s at least five."),
            Node("result", "Both values are four", "result", DescribeRole.Theorem,
                ClaimBody(), AssessedProvenance.FromRepo(Source),
                "Five robots in general position have distinct path coordinates. In row order their cycle coordinates form an arithmetic progression with step ±2 on the seven-cycle or ±3 on the ten-cycle. A legal move of five robots cannot change a cycle coordinate, so an unoccupied column remains unvisited. No six vertices are in general position. Four robots traverse two consecutive rows by four horizontal moves and their rotations; four vertical moves shift this traversal to the next row pair. The upper bound holds at every height, and the four-robot construction works at every height at least two.",
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("klavzar-et-al-2025-mobile-general-position-cylinders"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        DescribeRole role, Formula formula, AssessedProvenance provenance, string prose,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula X(string name) => F.Id(name);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula QCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(Seq(X(owner), Dot, X(name)))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(X(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(X(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LeqOf(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Not(Formula a) => Seq(Neg, Sp, Parenthesized(a));
    private static Formula InSet(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula GraphParameters(Formula body, bool decidable = true) => All("V", X("Type"),
        decidable ? Seq(OpenBracket, Call("DecidableEq", X("V")), CloseBracket, Comma, Sp,
            All("G", Call("SimpleGraph", X("V")), body)) : All("G", Call("SimpleGraph", X("V")), body));
    private static Formula Dist(string a, string b) => QCall("SimpleGraph", "dist", X("G"), X(a), X(b));
    private static Formula MemberAll(string v, Formula body) =>
        All(v, X("V"), Imp(InSet(X(v), X("S")), body));
    private static Formula GeneralPositionBody() => MemberAll("u", MemberAll("v", MemberAll("w",
        Imp(Ne(X("u"), X("v")), Imp(Ne(X("v"), X("w")), Imp(Ne(X("u"), X("w")),
            Not(Call("OnGeodesic", X("G"), X("u"), X("v"), X("w")))))))));
    private static Formula LegalMoveBody() => Ex("u", X("V"), And(InSet(X("u"), X("S")),
        Ex("v", X("V"), And(Not(InSet(X("v"), X("S"))),
            And(QCall("SimpleGraph", "Adj", X("G"), X("u"), X("v")),
                And(Eq(X("T"), Call("insert", X("v"), QCall("Finset", "erase", X("S"), X("u")))),
                    Call("IsGeneralPosition", X("G"), X("T"))))))));
    private static Formula At(Formula i) => new Formula.Apply(X("c"), [i]);
    private static Formula MobileBody() => And(Call("IsGeneralPosition", X("G"), X("S")),
        Ex("n", Nat(), Ex("c", new Formula.TypeArrow(Call("Fin", Add(X("n"), D(1))), Call("Finset", X("V"))),
            And(Eq(At(D(0)), X("S")),
                And(Parenthesized(All("i", Call("Fin", X("n")), Call("LegalMove", X("G"),
                        At(QCall("Fin", "castSucc", X("i"))), At(QCall("Fin", "succ", X("i")))))),
                    Parenthesized(All("x", X("V"), Ex("i", Call("Fin", Add(X("n"), D(1))), InSet(X("x"), At(X("i")))))))))));
    private static Formula ClaimBody() => All("s", Nat(), Imp(LeqOf(D(5), X("s")),
        And(Eq(Call("mobGP", Call("cylinder", D(7), X("s"))), D(4)),
            Eq(Call("mobGP", Call("cylinder", D(1, 0), X("s"))), D(4)))));
}
