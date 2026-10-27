using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.FiniteGeometry.Polytopes;

internal sealed class BaumelerTselentisWolfSourceDigraphPolytopeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S0/FiniteGeometry/Polytopes/BaumelerTselentisWolfSourceDigraphPolytope";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/FiniteGeometry/baumelertselentiswolf2025graphical");
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula First(Formula p) => App(Qualified("Prod", "fst"), p);
    private static Formula Second(Formula p) => App(Qualified("Prod", "snd"), p);
    private static Formula Receiver(Formula e) => Second(Call("val", e));
    private static Formula Arcs(Formula n)
    {
        var p = F.Id("p");
        return Seq(OpenBrace, p, Colon, Sp, Fin(n), Times, Sp, Fin(n), Mid,
            First(p), Neq, Sp, Second(p), CloseBrace);
    }
    private static Formula Vectors(Formula n) => new Formula.TypeArrow(Arcs(n), Real);
    private static Formula Sets(Formula n) => Call("Finset", Arcs(n));
    private static Formula SourceFormula()
    {
        var n = F.Id("n"); var a = F.Id("A"); var i = F.Id("i"); var e = F.Id("e");
        return All(n, Nat, All(a, Sets(n), Seq(Call("HasSource", a), Iff,
            Some(i, Fin(n), All(e, Arcs(n), Seq(e, InMacro, Sp, a, Implies, Sp, Receiver(e), Neq, Sp, i))))));
    }
    private static Formula HullFormula()
    {
        var n = F.Id("n"); var a = F.Id("A"); var x = F.Id("x"); var e = F.Id("e");
        var adjacency = Seq(Named("fun"), Sp, e, Colon, Sp, Arcs(n), Mapsto, Sp,
            Named("if"), Sp, e, InMacro, Sp, a, Sp, Named("then"), Sp, D(1), Sp, Named("else"), Sp, D(0));
        var vertices = Seq(OpenBrace, x, Colon, Sp, Vectors(n), Mid,
            Some(a, Sets(n), Seq(Call("HasSource", a), Land, Sp, x, Eq, Parenthesized(adjacency))), CloseBrace);
        return All(n, Nat, Seq(Call("sourcePolytope", n), Eq, Call("convexHull", Real, vertices)));
    }
    private static Formula InequalitiesFormula()
    {
        var n = F.Id("n"); var x = F.Id("x"); var e = F.Id("e");
        var f = F.Id("f"); var hf = F.Id("hf"); var i = F.Id("i");
        var noFixedPoint = All(i, Fin(n), Seq(Call("f", i), Neq, Sp, i));
        var arc = Seq(Langle, Parenthesized(Seq(Call("f", i), Comma, i)), Comma, Call("hf", i), Rangle);
        var sum = Seq(new Formula.Subscript(Sum, Seq(i, Colon, Sp, Fin(n))), Call("x", arc));
        var bounds = Seq(
            Parenthesized(All(e, Arcs(n), Seq(D(0), Leq, Sp, Call("x", e)))), Land,
            Parenthesized(Seq(D(3), Leq, Sp, n, Implies, Sp, All(e, Arcs(n), Seq(Call("x", e), Leq, Sp, D(1))))), Land,
            Parenthesized(All(f, new Formula.TypeArrow(Fin(n), Fin(n)), All(hf, Parenthesized(noFixedPoint),
                Seq(sum, Leq, Sp, Parenthesized(Seq(n, Colon, Sp, Real)), Minus, D(1))))));
        return All(n, Nat, Seq(Call("kefalopodaPolytope", n), Eq,
            OpenBrace, x, Colon, Sp, Vectors(n), Mid, Sp, bounds, CloseBrace));
    }
    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        return All(n, Nat, Seq(D(2), Leq, Sp, n, Implies,
            Call("kefalopodaPolytope", n), Eq, Call("sourcePolytope", n)));
    }
    private static DocumentBlock Node(string name, string title, Formula formula,
        AssessedProvenance provenance, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolutionClaim = null) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Module + "." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolutionClaim);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Trivial and kefalopoda inequalities describe every source-digraph polytope.",
        H("The Source-Digraph Polytope"), Blocks(
            Node("HasSource", "A source vertex", SourceFormula(), AssessedProvenance.FromLiterature(Source),
                "Page 17, Theorem 3: “The set of digraphs Γ(P_n^causal) is the set of all digraphs on n vertices with at least one source vertex:”. Vertices are Fin n; arcs are ordered pairs of distinct vertices. A source is a vertex that is never the receiver of an arc in A.", DescribeRole.Definition),
            Node("sourcePolytope", "The convex hull of source digraphs", HullFormula(), AssessedProvenance.FromLiterature(Source),
                "Page 17, Definition 8: “The polytope of source digraphs is Q_n^src := conv(Γ(P_n^causal)).” Section 2, page 6: “For a digraph D with V(D) = [n], we use α(D) ∈ {0, 1}^{n(n−1)} for the adjacency vector with α(D)_{i,j} = 1 ⇔ i j ∈ A(D).”. Finite arc sets describe all loopless digraphs, including the empty digraph; each adjacency coordinate is one for a present arc and zero otherwise. The convex hull is over the real numbers.", DescribeRole.Definition),
            Node("kefalopodaPolytope", "The three inequality families", InequalitiesFormula(), AssessedProvenance.FromLiterature(Source),
                "Page 24, Definition 13: “The polytope Q̃_n^src ⊆ ℝ^{n(n−1)} is the set of vectors that satisfy the following inequalities:” (58)–(60). These are coordinate nonnegativity, coordinate upper bounds for n ≥ 3, and one sum at most n − 1 for every fixed-point-free function. Page 17, Definition 9: “For any function f : [n] → [n] without fixed-points, i.e, with ∀i : f(i) ≠ i, the kefalopoda κ_f is” V(κ_f) = [n], A(κ_f) = {f(i) i | i ∈ [n]}. Thus f(i) is the sender and i the receiver; all sums count vertices once. The cast of n in the last bound is real.", DescribeRole.Definition),
            Node("claim", "The identity in every dimension", Seq(Named("claim"), Iff, Sp, Parenthesized(ClaimBody())), AssessedProvenance.FromLiterature(Source),
                "Page 24, after Definition 13: “We know that Q̃_n^src = Q_n^src for n ≤ 4. In general, this identity is unsolved.” The proposition asserts the identity for every natural n ≥ 2, with the three inequality families displayed above.", DescribeRole.Definition),
            Node("result", "The source-digraph polytope identity", ClaimBody(), AssessedProvenance.FromRepo(Source),
                "The kefalopoda sums bound the sum of the largest incoming coordinates by n − 1. Their complementary slacks give probabilities for the source vertex. Zeroing that source column and rescaling the others expresses each point as a convex mixture of fixed-source unit boxes. Each box is the convex hull of its zero-one source digraphs. For n = 2 the kefalopoda inequality and nonnegativity already imply the coordinate upper bounds.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("baumeler-tselentis-wolf-2025-source-digraph-polytope"),
                    ResolutionKind.Proved)))));
}
