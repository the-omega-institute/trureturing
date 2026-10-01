using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.VertexModels;

internal sealed class SimplexFixedPointFreePermutationsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/bardakov2024simplex");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For n > 2, a permutation without fixed points gives a solution of the n-simplex equation on every set exactly when n is even, and then the product of the transpositions of adjacent pairs of indices is such a solution. This answers Question 2 of V. Bardakov, B. Chuzinov, I. Emel'yanenkov, M. Ivanov, T. Kozlovskaya and V. Leshkov (arXiv:2206.08906; Question 4.22 of the journal version).",
        H("Fixed-point-free permutation solutions of the n-simplex equation"),
        Blocks(
            Node("edge", "The coordinates", EdgeFormula(),
                "The n-simplex equation acts on X^N with N = n(n+1)/2 coordinates, indexed by the edges {a, b}, a < b <= n, of the complete graph on the vertices 0, ..., n of the n-simplex. The paper numbers the coordinates by the rows of its matrix MI_n; row v of MI_n lists the edges at the vertex v in increasing order of the other endpoint, which is the order used below.",
                "Edge"),
            Node("slot", "The edges at a vertex", SlotFormula(),
                "For a vertex v in Fin (n + 1) and a slot j in Fin n, slotEdge(v, j) is the edge from v to the j-th of the other n vertices in increasing order: the vertex j when j < v, and j + 1 otherwise.",
                "slotEdge"),
            Node("op", "The vertex operators", OpFormula(),
                "For a map T from X^n to itself, R_v(T) applies T to the n coordinates on the edges at v, taken in slot order, and leaves the other coordinates unchanged. An edge (a, b) at v is in slot b - 1 when a = v and in slot a when b = v.",
                "opR"),
            Node("lhs", "The left side", LhsFormula(),
                "lhs(T, k) is the composition R_0(T) R_1(T) ... R_(k-1)(T) of the first k vertex operators, so that R_(k-1)(T) acts first; operators of vertices k > n are omitted.",
                "lhs"),
            Node("rhs", "The right side", RhsFormula(),
                "rhs(T, k) is the composition R_(k-1)(T) ... R_1(T) R_0(T) of the same operators in the reverse order.",
                "rhs"),
            Node("solution", "The n-simplex equation", SolutionFormula(),
                "T is a solution of the n-simplex equation when R_0 R_1 ... R_n = R_n ... R_1 R_0 as maps of X^N, as in the paper. The two sides are mutually reverse words, so the equation does not depend on the convention for applying a written product of operators.",
                "IsSolution"),
            Node("simple", "Simple maps", SimpleFormula(),
                "For a map s from Fin n to itself, the simple map of s sends (x_1, ..., x_n) to (x_s(1), ..., x_s(n)).",
                "simpleMap"),
            Node("claim", "Question 2", ClaimFormula(),
                "Question 2 of the paper asks: for which n > 2 are there non-identity permutations without fixed points that give solutions of the n-simplex equation? The statement answers it: such a permutation s of Fin n exists, with the simple map of s a solution on every type X, exactly when n is even. Here Perm(Fin n) is Equiv.Perm (Fin n) and Even is Nat's Even.",
                "claim"),
            Node("result", "Exactly the even n", Disp(F.Id("claim")),
                "The simple map of s acts on the coordinates by permuting edges: R_v(T_s) x = x composed with the map sigma_v that sends the edge in slot j at v to the edge in slot s(j) at v. So the two sides are x composed with sigma_n ... sigma_0 and with sigma_0 ... sigma_n, and T_s is a solution on every type exactly when these two edge maps agree. "
                + "Following the edge {i, i+1} through the vertices in increasing and in decreasing order gives the edges {s(i), s(i)+1} or {s(i), i}, and {s(i), s(i)+1} or {i+1, s(i)+1}; they agree only when |s(i) - i| <= 1. Conversely, if every index moves by at most one, every edge reaches the same edge in both orders, in one of three closed forms. "
                + "A permutation without fixed points that moves every index by one has displacements s(i) - i equal to +1 or -1 with sum 0, so n, the sum of the even numbers s(i) - i + 1, is even. For even n the involution exchanging 2t and 2t + 1 has no fixed point and moves every index by one, so its simple map is a solution.",
                "result",
                AssessedProvenance.FromRepo(Source),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bardakov-2024-simplex-fixed-point-free-permutations"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose, string declaration,
        AssessedProvenance? provenance = null, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("simplexperm-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance ?? AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula Lt(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThan, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, right);
    private static Formula AllIn(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, InMacro, Sp, domain, Comma, Sp, body);
    private static Formula Plus(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Minus(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula At(Formula f, params Formula[] arguments) => new Formula.Apply(f, [.. arguments]);
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);
    private static Formula Ite(Formula condition, Formula then, Formula otherwise) =>
        Call(F.Id("ite"), condition, then, otherwise);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula FinOf(Formula n) => Call(F.Id("Fin"), n);
    private static Formula Sub(Formula p, byte k) => new Formula.Subscript(p, D(k));

    private static Formula EdgeFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), n = F.Id("n");
        Formula condition = And(Lt(a, b), Rel(b, FormulaRelationOperator.LessThanOrEqual, n));
        Formula set = Seq(OpenBrace, Pair(a, b), Sp, InMacro, Sp, Nat(), Sp, Times, Sp, Nat(), Sp,
            Colon, Sp, condition, CloseBrace);
        return Disp(Equal(Call(F.Id("Edge"), n), set));
    }

    private static Formula SlotFormula()
    {
        Formula v = F.Id("v"), j = F.Id("j");
        return Disp(Equal(Call(F.Id("slotEdge"), v, j),
            Ite(Lt(j, v), Pair(j, v), Pair(v, Plus(j, D(1))))));
    }

    private static Formula OpFormula()
    {
        Formula t = F.Id("T"), v = F.Id("v"), x = F.Id("x"), e = F.Id("e"), j = F.Id("j");
        Formula block = Seq(Open, j, Sp, Mapsto, Sp, At(x, Call(F.Id("slotEdge"), v, j)), Close);
        Formula applied = At(t, block);
        Formula value = Ite(Equal(Sub(e, 1), v), At(applied, Minus(Sub(e, 2), D(1))),
            Ite(Equal(Sub(e, 2), v), At(applied, Sub(e, 1)), At(x, e)));
        return Disp(Equal(At(Call(F.Id("opR"), t, v, x), e), value));
    }

    private static Formula LhsFormula()
    {
        Formula t = F.Id("T"), k = F.Id("k");
        return Disp(Seq(Equal(Call(F.Id("lhs"), t, D(0)), Named(F.Id("id"))), Comma, Qquad,
            Equal(Call(F.Id("lhs"), t, Plus(k, D(1))),
                Seq(Call(F.Id("lhs"), t, k), Sp, Circ, Sp, Call(F.Id("opR"), t, k)))));
    }

    private static Formula RhsFormula()
    {
        Formula t = F.Id("T"), k = F.Id("k");
        return Disp(Seq(Equal(Call(F.Id("rhs"), t, D(0)), Named(F.Id("id"))), Comma, Qquad,
            Equal(Call(F.Id("rhs"), t, Plus(k, D(1))),
                Seq(Call(F.Id("opR"), t, k), Sp, Circ, Sp, Call(F.Id("rhs"), t, k)))));
    }

    private static Formula SolutionFormula()
    {
        Formula t = F.Id("T"), n = F.Id("n");
        return Disp(Iff(Call(F.Id("IsSolution"), n, t),
            Equal(Call(F.Id("lhs"), t, Plus(n, D(1))), Call(F.Id("rhs"), t, Plus(n, D(1))))));
    }

    private static Formula SimpleFormula()
    {
        Formula s = F.Id("s"), y = F.Id("y"), j = F.Id("j");
        return Disp(Equal(At(Call(F.Id("simpleMap"), s, y), j), At(y, At(s, j))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), s = F.Id("s"), i = F.Id("i"), x = F.Id("X");
        Formula noFixed = Seq(Forall, Sp, i, Comma, Sp,
            Rel(At(s, i), FormulaRelationOperator.NotEqual, i));
        Formula solves = Seq(Forall, Sp, x, Comma, Sp,
            Call(F.Id("IsSolution"), n, Call(F.Id("simpleMap"), s)));
        Formula exists = Seq(Exists, Sp, s, Sp, InMacro, Sp, Call(F.Id("Perm"), FinOf(n)), Comma, Sp,
            And(noFixed, solves));
        Formula body = AllIn(n, Nat(), Implies(Lt(D(2), n),
            Parenthesized(Iff(Parenthesized(exists), Call(F.Id("Even"), n)))));
        return Disp(Iff(F.Id("claim"), body));
    }
}
