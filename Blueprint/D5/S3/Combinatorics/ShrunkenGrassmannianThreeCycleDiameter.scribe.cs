using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ShrunkenGrassmannianThreeCycleDiameterDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/CayleyGrowth/chervov2026cayleypy4");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For 2 <= L <= N and N > 3, on binary words with L zeros and N - L ones, where a move rotates three consecutive letters one place in either direction, every word can be turned into every other in at most the ceiling of L(N - L)/2 moves, and turning the sorted word 0...01...1 into its reversal needs that many, as conjectured for k = 3 in Conjecture 16 of CayleyPy-4.",
        H("Diameter of the inverse-closed consecutive 3-cycle Schreier coset graph"),
        Blocks(
            Node("rotl", "The consecutive cycle on a window", RotFormula("rotL", D(1)),
                "The cycle (i, i + 1, ..., i + k - 1) acts on a word by rotating the window of length k starting at position i one place to the left: the letters a_1, a_2, ..., a_k of the window become a_2, ..., a_k, a_1.",
                "rotL", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rotr", "The inverse cycle", RotFormula("rotR", Subtract(F.Id("k"), D(1))),
                "The inverse cycle rotates the same window one place to the right: a_1, ..., a_(k-1), a_k become a_k, a_1, ..., a_(k-1).",
                "rotR", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("step", "Edges of the inverse-closed graph", StepFormula(),
                "Two words are adjacent when some window of k consecutive positions lies inside the word and one word arises from the other by the cycle or its inverse on that window.",
                "Step", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("reach", "Reachability within m moves", ReachFormula(),
                "Reach(k, m, x, y) says that y is reached from x in at most m moves: with no move only x itself, and with m + 1 moves every word reached within m moves together with every neighbour of such a word.",
                "Reach", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("vertex", "Vertices of the coset graph", VertexFormula(),
                "The vertices of the Schreier coset graph of S_N / (S_L x S_(N - L)) are the words of length N with exactly L zeros.",
                "IsVertex", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ecc", "Largest distance from the central state", EccFormula(),
                "The least m such that every vertex is reached from the central state within m moves. The central state [0]^L + [1]^(N - L), L zeros followed by N - L ones, is normalWord(L, N - L) of D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange, reused here. This is the quantity CayleyPy's growth computation reports as the diameter of a coset graph.",
                "ecc", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("diam", "Diameter", DiamFormula(),
                "The least m such that every vertex is reached from every vertex within m moves, the diameter in the graph-theoretic sense.",
                "diam", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("claim", "The k = 3 clause of Conjecture 16", ClaimDefinitionFormula(),
                "Conjecture 16 of the source (inverse-closed case), clause k = 3: for L >= 2 the diameter is the ceiling of L(N - L)/2, which equals the floor of (L(N - L) + 1)/2. Both readings of the diameter are included, for N > 3 because the source takes n > k.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the k = 3 clause", Disp(F.Id("claim")),
                "Lower bound: count the inversions, the pairs of positions p < q holding a one at p and a zero at q. A rotation of three consecutive letters leaves the pairs outside the window and the pairs across its boundary unchanged, so it changes the count by at most 2. The central state has no inversion and its reversal, the N - L ones followed by the L zeros, has L(N - L), so reaching the reversal from the central state takes at least the ceiling of L(N - L)/2 moves. Upper bound, from any vertex x to any vertex y, by induction on N from N = 3, where the three arrangements are pairwise one rotation apart. Let b be the last letter of y and let rho be the number of letters after the last b in x. Moving that b across them, two places per move and with one final move when rho is odd, costs the ceiling of rho/2 moves, after which the first N - 1 letters are handled by induction. With M = N - L, this fits the budget for b = 1, where rho <= L, unless L is odd, M is even and rho = L, and for b = 0, where rho <= M, unless M is odd, L is even and rho = M. In these two cases x ends in the other letter, so the same peeling from y to x fits the budget for that letter, and a path from y to x reversed is a path from x to y.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("chervov-2026-cayleypy4-three-cycle-grassmannian-diameter"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("cayley3-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Words() => Call("List", F.Id("Bool"));
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
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Ex(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Append(Formula left, Formula right) => Call("append", left, right);

    private static Formula RotFormula(string name, Formula shift)
    {
        Formula k = F.Id("k"), i = F.Id("i"), x = F.Id("x");
        Formula window = Call("take", k, Call("drop", i, x));
        Formula body = Append(Append(Call("take", i, x), Call("rotate", window, shift)),
            Call("drop", Add(i, k), x));
        return Disp(Equal(Call(name, k, i, x), body));
    }

    private static Formula StepFormula()
    {
        Formula k = F.Id("k"), i = F.Id("i"), x = F.Id("x"), y = F.Id("y");
        Formula body = Ex("i", Naturals(), And(AtMost(Add(i, k), Call("length", x)),
            Or(Equal(y, Call("rotL", k, i, x)), Equal(y, Call("rotR", k, i, x)))));
        return Disp(Iff(Call("Step", k, x, y), body));
    }

    private static Formula ReachFormula()
    {
        Formula k = F.Id("k"), m = F.Id("m"), x = F.Id("x"), y = F.Id("y"), z = F.Id("z");
        Formula zero = Iff(Call("Reach", k, D(0), x, y), Equal(y, x));
        Formula succ = Iff(Call("Reach", k, Add(m, D(1)), x, y),
            Or(Call("Reach", k, m, x, y),
                Ex("z", Words(), And(Call("Reach", k, m, x, z), Call("Step", k, z, y)))));
        return Disp(And(Parenthesized(zero), Parenthesized(succ)));
    }

    private static Formula VertexFormula()
    {
        Formula l = F.Id("L"), n = F.Id("N"), x = F.Id("x");
        return Disp(Iff(Call("IsVertex", l, n, x),
            And(Equal(Call("length", x), n), Equal(Call("count", F.Id("false"), x), l))));
    }

    private static Formula Least(Formula condition) =>
        Call("sInf", Seq(OpenBrace, F.Id("m"), InMacro, Naturals(), Colon, condition, CloseBrace));

    private static Formula EccFormula()
    {
        Formula k = F.Id("k"), l = F.Id("L"), n = F.Id("N"), m = F.Id("m"), y = F.Id("y");
        Formula condition = All("y", Words(), Implies(Call("IsVertex", l, n, y),
            Call("Reach", k, m, Call("normalWord", l, Subtract(n, l)), y)));
        return Disp(Equal(Call("ecc", k, l, n), Least(condition)));
    }

    private static Formula DiamFormula()
    {
        Formula k = F.Id("k"), l = F.Id("L"), n = F.Id("N"), m = F.Id("m"), x = F.Id("x"), y = F.Id("y");
        Formula condition = All("x", Words(), All("y", Words(),
            Implies(And(Call("IsVertex", l, n, x), Call("IsVertex", l, n, y)), Call("Reach", k, m, x, y))));
        return Disp(Equal(Call("diam", k, l, n), Least(condition)));
    }

    private static Formula ClaimBody()
    {
        Formula l = F.Id("L"), n = F.Id("N");
        Formula value = new Formula.Floor(new Formula.Fraction(Add(Times(l, Parenthesized(Subtract(n, l))), D(1)), D(2)));
        Formula conclusion = And(Equal(Call("ecc", D(3), l, n), value), Equal(Call("diam", D(3), l, n), value));
        return All("L", Naturals(), All("N", Naturals(), Implies(
            And(And(AtMost(D(2), l), AtMost(l, n)), Less(D(3), n)), conclusion)));
    }

    private static Formula ClaimDefinitionFormula() => Disp(
        new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())));
}
