using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.KyFanGap;

internal sealed class HarithaChithraDistanceSeidelEnergyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/KyFanGap/HarithaChithraDistanceSeidelEnergy.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/harithachithra2022distanceseidel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deleting any edge of a complete bipartite graph with both parts of size at least two strictly increases its distance Seidel energy for the matrix J - I - 2D.",
        H("Distance Seidel energy after deleting an edge"), Blocks(
            Node("matrix", "Distance Seidel matrix", "distSeidel", MatrixFormula(),
                "Page 2: \"D^S(G) = J − I − 2D = −1 if v_r is adjacent to v_t, 1 − 2d_G(v_r, v_t) otherwise.\" The displayed expression encodes J − I − 2D entrywise using SimpleGraph.dist, with zero diagonal. The source's casewise expression instead gives diagonal one. Only the matrix equation is used here. On the complete bipartite graphs and their single-edge deletions considered below, every pair is connected.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Problem 5.1", "claim", Equal(Call("claim"), Parenthesized(ClaimBody())),
                "Problem 5.1, page 13: \"Let G = K_{a,b}, with a, b > 1. Is E_{D^S}(K_{a,b} − e) > E_{D^S}(K_{a,b}), for any edge e of K_{a,b}?\" The proposition gives the affirmative universal statement. The vertex type is Fin a ⊕ Fin b; edges are unordered pairs in the edge set. The natural-number inequalities 2 ≤ a and 2 ≤ b express a, b > 1. SimpleGraph.deleteEdges removes the singleton edge set.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Strict increase for every edge", "result", ClaimBody(),
                "The distance Seidel matrix of the complete bipartite graph has energy 6(a+b−2). Its sign is a symmetric involution which reflects the two part-indicator directions. Deleting an edge changes only the two corresponding off-diagonal entries, each by −4. This preserves the supporting trace functional. Equality in the trace bound for the sum of absolute eigenvalues would force commutation with the involution, whereas a commutator entry is 8/a at another vertex of the first part. Since a ≥ 2, that entry is nonzero and the energy inequality is strict. The proof treats every a,b ≥ 2, including the cases a = 2 and a = 3 of Propositions 5.2–5.3. It makes no universal assertion about the alternative diagonal-one matrix.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("haritha-chithra-2022-distance-seidel-energy-problem-5-1"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("hc-distance-seidel-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Qualified(string name)
    {
        var parts = name.Split('.');
        var tokens = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (tokens.Count != 0) tokens.Add(Dot);
            tokens.Add(F.Id(part));
        }
        return Seq([.. tokens]);
    }
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(Qualified(name)))
        : new Formula.Apply(Seq(Operatorname, Grp(Qualified(name))), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(Call("fun"), Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Inst(string name, Formula type) => Seq(OpenBracket, Call(name, type), CloseBracket, Sp);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula V() => F.Id("V");
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula K(Formula a, Formula b) => Call("completeBipartiteGraph", Fin(a), Fin(b));
    private static Formula DS(Formula g) => Call("distSeidel", g);
    private static Formula Energy(Formula m) => Call("energy", m);
    private static Formula CarrierBinders(Formula body) => All("V", F.Id("Type"),
        Seq(Inst("Fintype", V()), Inst("DecidableEq", V()), body));

    private static Formula MatrixFormula()
    {
        Formula g = F.Id("G"), u = F.Id("u"), v = F.Id("v");
        var distance = Parenthesized(Seq(Call("SimpleGraph.dist", g, u, v), Sp, Colon, Sp, Real()));
        var entry = new Formula.Binary(new Formula.Binary(D(1), FormulaBinaryOperator.Subtract,
            Call("ite", Parenthesized(Equal(u, v)), D(1), D(0))), FormulaBinaryOperator.Subtract,
            new Formula.Binary(D(2), FormulaBinaryOperator.Multiply, distance));
        return CarrierBinders(All("G", Call("SimpleGraph", V()),
            Equal(DS(g), Call("Matrix.of", Lam("u", V(), Lam("v", V(), entry))))));
    }
    private static Formula ClaimBody()
    {
        Formula a = F.Id("a"), b = F.Id("b"), e = F.Id("e");
        var graph = K(a, b);
        var vertices = Call("Sum", Fin(a), Fin(b));
        var member = new Formula.Relation(e, FormulaRelationOperator.MemberOf, Call("SimpleGraph.edgeSet", graph));
        var deleted = Call("SimpleGraph.deleteEdges", graph, Seq(OpenBrace, e, CloseBrace));
        var inequality = new Formula.Relation(Energy(DS(graph)), FormulaRelationOperator.LessThan, Energy(DS(deleted)));
        return All("a", Nat(), All("b", Nat(), Implies(new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, a),
            Implies(new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, b),
                All("e", Call("Sym2", vertices), Implies(member, inequality))))));
    }
}
