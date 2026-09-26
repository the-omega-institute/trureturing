using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class OrientedCirculantZeroTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Dynamics/OrientedCirculantZeroTransfer.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/song2026zerotransfer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "On the connected oriented circulant graph G(Z_30, {5, 6, 9, 20}) the continuous-time quantum walk never moves amplitude between the vertex 0 and the even vertex 2, so the parity restriction conjectured for orders n = 2 (mod 4) fails at n = 30.",
        H("Song and Lin's parity conjecture for zero transfer is false"),
        Blocks(
            Node("hermitian-adjacency", "The Hermitian adjacency matrix", HermAdjFormula(),
                "For a connection set C in Z_n the circulant graph has an arc from a to b when b - a lies in C. The Hermitian adjacency matrix has entry i on arcs, -i on reversed arcs and 0 elsewhere; for an oriented connection set no pair carries both.",
                "hermAdj", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("transition", "The transition matrix", TransitionFormula(),
                "The continuous-time quantum walk at real time t is the matrix exponential U(t) = exp(-i t H).",
                "transition", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("zero-transfer", "Zero transfer", ZeroTransferFormula(),
                "The graph has zero transfer from u to v when the (u, v) entry of U(t) vanishes at every time t >= 0.",
                "ZeroTransfer", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("oriented", "Oriented connection sets", OrientedFormula(),
                "The connection set avoids 0 and contains no element together with its negative.",
                "Oriented", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("connected", "Connectedness", ConnectedFormula(),
                "The underlying undirected graph, which joins distinct a and b when b - a or a - b lies in C, is connected.",
                "Connected", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture", ClaimDefinitionFormula(),
                "For every order n = 2 (mod 4), every oriented connection set with connected graph and every vertex v, zero transfer between v and 0 in both directions forces the representative of v in 0, ..., n - 1 to be odd. Reading zero transfer between v and 0 in both directions only strengthens the hypothesis.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The counterexample n = 30, C = {5, 6, 9, 20}, v = 2", Disp(new Formula.Not(F.Id("claim"))),
                "The set C is oriented, and 6 - 5 = 1 connects every vertex a to a + 1 through a + 6, so the graph is connected. H is i times the integer skew-symmetric matrix S with entry 1 on arcs and -1 on reversed arcs, so every power of H is a power of i times the corresponding power of S. Seven exact row products give the rows r_k of S^k at vertex 0 for k <= 7; they satisfy r_k(2) = 0 for k <= 6 and r_7 = -32 r_5 - 320 r_3 - 960 r_1. Multiplying by S propagates this relation to r_(k+7) for every k, so strong induction gives (S^k)(0, 2) = 0 for all k, and skew-symmetry gives (S^k)(2, 0) = (-1)^k (S^k)(0, 2) = 0. Each term of the exponential series of -i t H therefore has vanishing (0, 2) and (2, 0) entries, so U(t) has them too at every time, and zero transfer holds between 0 and the even vertex 2.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("song-lin-2026-oriented-circulant-zero-transfer-parity-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("song-lin-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Named(string name)
    {
        var tokens = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (tokens.Count > 0) tokens.Add(Dot);
            tokens.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. tokens])));
    }
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula ZMod(Formula n) => Call("ZMod", n);
    private static Formula Entry(Formula matrix, Formula row, Formula column) =>
        new Formula.Subscript(Parenthesized(matrix), Seq(row, Comma, Sp, column));

    private static Formula HermAdjFormula()
    {
        Formula n = F.Id("n"), c = F.Id("C"), a = F.Id("a"), b = F.Id("b"), i = F.Id("i");
        Formula value = Call("ite", Member(Subtract(b, a), c), i,
            Call("ite", Member(Subtract(a, b), c), new Formula.Negate(i), D(0)));
        return Disp(All("a", ZMod(n), All("b", ZMod(n),
            Equal(Entry(Call("hermAdj", n, c), a, b), value))));
    }

    private static Formula TransitionFormula()
    {
        Formula n = F.Id("n"), c = F.Id("C"), t = F.Id("t"), i = F.Id("i");
        return Disp(All("t", Reals(), Equal(Call("transition", n, c, t),
            Call("NormedSpace.exp", Times(new Formula.Negate(Times(i, t)), Call("hermAdj", n, c))))));
    }

    private static Formula ZeroTransferFormula()
    {
        Formula n = F.Id("n"), c = F.Id("C"), t = F.Id("t"), u = F.Id("u"), v = F.Id("v");
        return Disp(Iff(Call("ZeroTransfer", n, c, u, v), All("t", Reals(),
            Implies(AtMost(D(0), t), Equal(Entry(Call("transition", n, c, t), u, v), D(0))))));
    }

    private static Formula OrientedFormula()
    {
        Formula c = F.Id("C"), x = F.Id("x");
        return Disp(Iff(Call("Oriented", c), And(new Formula.Not(Member(D(0), c)),
            All("x", c, new Formula.Not(Member(new Formula.Negate(x), c))))));
    }

    private static Formula ConnectedFormula()
    {
        Formula c = F.Id("C"), a = F.Id("a"), b = F.Id("b");
        Formula graph = Call("SimpleGraph.fromRel", Call("arc", c));
        Formula arcs = All("a", ZMod(F.Id("n")), All("b", ZMod(F.Id("n")),
            Iff(Call("arc", c, a, b), Member(Subtract(b, a), c))));
        return Disp(And(arcs, Iff(Call("Connected", c), Call("SimpleGraph.Connected", graph))));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n"), c = F.Id("C"), v = F.Id("v");
        Formula transfer = And(Call("ZeroTransfer", n, c, v, D(0)), Call("ZeroTransfer", n, c, D(0), v));
        Formula vertex = All("v", ZMod(n), Implies(transfer, Call("Odd", Call("ZMod.val", v))));
        Formula sets = All("C", Call("Finset", ZMod(n)),
            Implies(Call("Oriented", c), Implies(Call("Connected", c), vertex)));
        return All("n", Naturals(), Implies(Equal(Call("NatMod", n, D(4)), D(2)), sets));
    }

    private static Formula ClaimDefinitionFormula() => Disp(
        new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())));
}
