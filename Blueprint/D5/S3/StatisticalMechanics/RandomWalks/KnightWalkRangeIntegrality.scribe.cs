using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.RandomWalks;

internal sealed class KnightWalkRangeIntegralityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/RandomWalks/KnightWalkRangeIntegrality.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/sloane2019a309221");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a knight's random walk on the infinite chessboard, with each of the eight moves chosen uniformly at every step, the expected number E(n) of distinct squares visited in n steps (the start included) satisfies: E(n) 2^(3n-3) is an integer for every n at least one (OEIS A309221).",
        H("The normalized expected range of a knight's random walk is an integer"),
        Blocks(
            Node("move", "The eight knight moves", MoveFormula(),
                "The eight moves of a knight on the square lattice, listed counterclockwise from (1, 2); the walk chooses one of them uniformly at each step.",
                "move", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("position", "The position after j steps", PositionFormula(),
                "The sum of the first j moves of a step sequence w of length n, starting from the origin.",
                "position", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("visited", "The visited squares", VisitedFormula(),
                "The positions after 0, 1, ..., n steps; OEIS A326954: \"The starting square is always considered part of the walk.\"",
                "visited", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("expected-range", "The expected number of distinct visited squares", ExpectedFormula(),
                "OEIS A326954 and A326955: \"the expected number of distinct squares visited by a knight's random walk on an infinite chessboard after n steps\"; all 8^n step sequences are equally likely.",
                "expectedRange", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture of OEIS A309221", ClaimDefinitionFormula(),
                "OEIS A309221, COMMENTS: \"a(0)=1; for n>0, a(n) = (A326954(n)/A326955(n))*2^(3*n-3). (It is only a conjecture that this is always an integer).\" The claim is the integrality of a(n) for every n at least one.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Integrality by the symmetries of the eight moves", ClaimFormula(),
                "The eight symmetries of the square lattice permute the eight moves simply transitively: for each move m there is a signed coordinate permutation g of the lattice and a permutation s of the moves with g(move i) = move(s(i)) and s(0) = m. Applying s to every step maps the positions of a walk by g, hence its visited squares by g, and g is injective, so the number of visited squares is unchanged. For n = k + 1, split the step sequences by their first step; applying s maps the walks starting with move 0 bijectively onto those starting with move m, so each of the eight classes has the same total T. The total over all walks is 8T, and E(k + 1) 2^(3k) = 8T / 8^(k+1) 8^k = T is an integer.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("sloane-2019-a309221-knight-walk-range-integrality"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("knight-walk-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula IntegersSet() => Seq(Mathbb, Grp(F.Id("Z")));
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
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Some(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Neg(byte d) => Seq(Minus, D(d));
    private static Formula Pair(Formula x, Formula y) => Seq(Open, x, Comma, Sp, y, Close);
    private static Formula Walks(Formula n) => Seq(Call("Fin", n), Sp, To, Sp, Call("Fin", D(8)));

    private static Formula MoveFormula()
    {
        Formula[] moves =
        [
            Pair(D(1), D(2)), Pair(D(2), D(1)), Pair(D(2), Neg(1)), Pair(D(1), Neg(2)),
            Pair(Neg(1), Neg(2)), Pair(Neg(2), Neg(1)), Pair(Neg(2), D(1)), Pair(Neg(1), D(2)),
        ];
        var items = new List<Formula> { OpenBracket };
        for (int k = 0; k < moves.Length; k++)
        {
            if (k > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(moves[k]);
        }
        items.Add(CloseBracket);
        return Disp(Equal(Named("move"), Seq([.. items])));
    }

    private static Formula PositionFormula()
    {
        Formula n = F.Id("n"), w = F.Id("w"), j = F.Id("j"), i = F.Id("i");
        Formula sum = Seq(Sum, Underscore, Grp(Member(i, Call("Fin", n)), Comma, Sp, Less(i, j)), Sp,
            Call("move", new Formula.Apply(w, [i])));
        return Disp(All("n", Naturals(), All("w", Walks(n), All("j", Naturals(),
            Equal(Call("position", w, j), sum)))));
    }

    private static Formula VisitedFormula()
    {
        Formula n = F.Id("n"), w = F.Id("w"), j = F.Id("j");
        Formula set = Seq(OpenBrace, Call("position", w, j), Sp, Mid, Sp,
            Member(j, Call("range", Add(n, D(1)))), CloseBrace);
        return Disp(All("n", Naturals(), All("w", Walks(n), Equal(Call("visited", w), set))));
    }

    private static Formula ExpectedFormula()
    {
        Formula n = F.Id("n"), w = F.Id("w");
        Formula sum = Seq(Sum, Underscore, Grp(Member(w, Walks(n))), Sp, Call("card", Call("visited", w)));
        return Disp(All("n", Naturals(), Equal(Call("expectedRange", n),
            new Formula.Fraction(sum, new Formula.Power(D(8), n)))));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n"), m = F.Id("m");
        Formula exponent = Subtract(Mul(D(3), n), D(3));
        Formula value = Mul(Call("expectedRange", n), new Formula.Power(D(2), exponent));
        return All("n", Naturals(), Implies(AtMost(D(1), n), Some("m", IntegersSet(), Equal(value, m))));
    }

    private static Formula ClaimDefinitionFormula() => Disp(
        new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())));

    private static Formula ClaimFormula() => Disp(F.Id("claim"));
}
