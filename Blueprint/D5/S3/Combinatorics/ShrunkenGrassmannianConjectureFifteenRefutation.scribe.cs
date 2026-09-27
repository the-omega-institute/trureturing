using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ShrunkenGrassmannianConjectureFifteenRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/ShrunkenGrassmannianConjectureFifteenRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/CayleyGrowth/chervov2026cayleypy4");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The k = 5 clause of Conjecture 15 of CayleyPy-4 is false: without inverses, rotations of five consecutive letters need at least 9 moves to turn 0000111111111 into its reversal, whichever way the rotation acts, while the clause gives 8.",
        H("Conjecture 15 of CayleyPy-4 fails at k = 5, L = 4, N = 13"),
        Blocks(
            Node("step", "Directed moves", StepFormula(),
                "Without inverses a move applies the cycle on a window of k consecutive positions, which rotates the window one place left or one place right depending on the convention for the action of a permutation on a word; the flag left selects the convention.",
                "StepDir", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("reach", "Directed reachability within m moves", ReachFormula(),
                "ReachDir(left, k, m, x, y) says that y is reached from x in at most m directed moves.",
                "ReachDir", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("ecc", "Largest directed distance from the central state", EccFormula(),
                "The least m such that every vertex is reached from the central state within m directed moves. A vertex is a word of length N with exactly L zeros (IsVertex(L, N, x)); the central state [0]^L + [1]^(N - L), L zeros followed by N - L ones, is normalWord(L, N - L) of D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange. IsVertex, rotL and rotR are reused from D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter.",
                "eccDir", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("diam", "Directed diameter", DiamFormula(),
                "The least m such that every vertex is reached from every vertex within m directed moves.",
                "diamDir", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("clause", "The k = 5 clause of Conjecture 15", ClauseFormula(),
                "For all L >= 4 and N >= L + 9, with t + 1 = N - L, the diameter is L times the floor of (t + 1)/4, plus 1 when t + 1 is divisible by 4.",
                "clauseFive", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The clause for some convention and reading", ClaimFormula(),
                "The clause holds for one of the two conventions and one of the two readings of the diameter.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Refutation", Disp(new Formula.Not(F.Id("claim"))),
                "Count the inversions of a word, the pairs of positions holding a one before a zero. Rotating five consecutive letters one place carries one letter past the other four, so it changes the count by at most 4, and a directed move is in either convention such a rotation. The central state 0000111111111 has no inversion and its reversal 1111111110000 has 36, so reaching the reversal takes at least 9 moves. If the central eccentricity or the diameter were 8 at L = 4, N = 13 in either convention, the least element of its defining set would be 8, and the reversal, a vertex, would be within 8 moves of the central state, also a vertex. The clause gives 4 times the floor of 9/4, which is 8, since 9 is not divisible by 4.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("chervov-2026-cayleypy4-conjecture-fifteen-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("cayley15-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Words() => Call("List", F.Id("Bool"));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
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
    private static Formula IfThenElse(Formula condition, Formula yes, Formula no) =>
        Seq(Named("if"), Sp, condition, Sp, Named("then"), Sp, yes, Sp, Named("else"), Sp, no);
    private static Formula Least(Formula condition) =>
        Call("sInf", Seq(OpenBrace, F.Id("m"), InMacro, Naturals(), Colon, condition, CloseBrace));

    private static Formula StepFormula()
    {
        Formula left = F.Id("left"), k = F.Id("k"), i = F.Id("i"), x = F.Id("x"), y = F.Id("y");
        Formula body = Ex("i", Naturals(), And(AtMost(Add(i, k), Call("length", x)),
            Equal(y, Parenthesized(IfThenElse(left, Call("rotL", k, i, x), Call("rotR", k, i, x))))));
        return Disp(Iff(Call("StepDir", left, k, x, y), body));
    }

    private static Formula ReachFormula()
    {
        Formula left = F.Id("left"), k = F.Id("k"), m = F.Id("m"), x = F.Id("x"), y = F.Id("y"), z = F.Id("z");
        Formula zero = Iff(Call("ReachDir", left, k, D(0), x, y), Equal(y, x));
        Formula succ = Iff(Call("ReachDir", left, k, Add(m, D(1)), x, y),
            Or(Call("ReachDir", left, k, m, x, y),
                Ex("z", Words(), And(Call("ReachDir", left, k, m, x, z), Call("StepDir", left, k, z, y)))));
        return Disp(And(Parenthesized(zero), Parenthesized(succ)));
    }

    private static Formula EccFormula()
    {
        Formula left = F.Id("left"), k = F.Id("k"), l = F.Id("L"), n = F.Id("N"), m = F.Id("m"), y = F.Id("y");
        Formula condition = All("y", Words(), Implies(Call("IsVertex", l, n, y),
            Call("ReachDir", left, k, m, Call("normalWord", l, Subtract(n, l)), y)));
        return Disp(Equal(Call("eccDir", left, k, l, n), Least(condition)));
    }

    private static Formula DiamFormula()
    {
        Formula left = F.Id("left"), k = F.Id("k"), l = F.Id("L"), n = F.Id("N"), m = F.Id("m"), x = F.Id("x"), y = F.Id("y");
        Formula condition = All("x", Words(), All("y", Words(),
            Implies(And(Call("IsVertex", l, n, x), Call("IsVertex", l, n, y)), Call("ReachDir", left, k, m, x, y))));
        return Disp(Equal(Call("diamDir", left, k, l, n), Least(condition)));
    }

    private static Formula ClauseFormula()
    {
        Formula l = F.Id("L"), n = F.Id("N"), d = F.Id("D");
        Formula gap = Parenthesized(Subtract(n, l));
        Formula value = Add(Times(l, new Formula.Floor(new Formula.Fraction(Subtract(n, l), D(4)))),
            Parenthesized(IfThenElse(Equal(new Formula.Modulo(gap, D(4)), D(0)), D(1), D(0))));
        return Disp(Iff(Call("clauseFive", d), All("L", Naturals(), All("N", Naturals(), Implies(
            And(AtMost(D(4), l), AtMost(Add(l, D(9)), n)),
            Equal(new Formula.Apply(d, [D(5), l, n]), value))))));
    }

    private static Formula ClaimFormula() => Disp(Iff(F.Id("claim"),
        Ex("left", F.Id("Bool"), Or(Call("clauseFive", Call("eccDir", F.Id("left"))),
            Call("clauseFive", Call("diamDir", F.Id("left")))))));
}
