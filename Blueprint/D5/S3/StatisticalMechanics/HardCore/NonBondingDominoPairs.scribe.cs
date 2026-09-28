using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class NonBondingDominoPairsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/HardCore/NonBondingDominoPairs.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/mathar2024nonbonding");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two dominoes on the r × c board are non-bonding when every square of one is at L1 distance at least 2 from every square of the other, so that they share at most a corner point: hard dimers with nearest-neighbour exclusion. For r, c at least 3 the sets of two non-bonding dominoes number 2c^2r^2 - 2(cr^2 + c^2r) + (r^2 + c^2)/2 - 22cr + (59/2)(c + r) - 30, as conjectured by R. J. Mathar (Conjecture 1 of arXiv:2404.18806).",
        H("Two non-bonding dominoes on a rectangular board"),
        Blocks(
            Node("domino", "Dominoes", DominoFormula(),
                "A domino on the r × c board is a set of two squares (p1, p2), (q1, q2) of the board, with p1, q1 < r and p2, q2 < c, at L1 distance 1; dist is the distance of natural numbers, |a - b|.",
                "IsDomino", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("nonbonding", "Non-bonding dominoes", NonBondingFormula(),
                "Two dominoes are non-bonding when every square of one has L1 distance at least 2 from every square of the other; this is the criterion of the paper, and it forces them to be disjoint.",
                "NonBonding", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("count", "Placements of two dominoes", CountFormula(),
                "D(r, c, 2) is the number of sets of two dominoes on the board that are non-bonding (Definition 1 of the paper with d = 2).",
                "D2", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Mathar's Conjecture 1", ClaimFormula(),
                "For all r and c at least 3, D(r, c, 2) is the stated biquadratic polynomial (equation (21) of the paper), read in the rationals.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the conjecture", Disp(F.Id("claim")),
                "Every domino is a horizontal one anchored at (i, j) with i < r, j < c - 1 or a vertical one anchored at (i, j) with i < r - 1, j < c, and these anchors determine it. Two dominoes bond (some squares at L1 distance at most 1) exactly when the offset of their anchors lies in a finite list: 11 offsets for two horizontal or two vertical dominoes, the equal one included, and 12 for a horizontal and a vertical one. The ordered anchor pairs with a given offset (a, b) are a product of two interval overlaps, for instance (r - |a|)(c - 1 - |b|) for two horizontal dominoes, and for r, c at least 3 each overlap is linear. Twice D(r, c, 2) is the number of ordered non-bonding pairs, N^2 minus the 46 offset classes with N = r(c - 1) + (r - 1)c the number of dominoes, which sums to the stated polynomial.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mathar-2024-nonbonding-domino-pairs"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("nbdomino-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
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
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Ex(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Sub(Formula value, int index) => new Formula.Subscript(value, D((byte)index));
    private static Formula Square(Formula value) => new Formula.Power(value, D(2));
    private static Formula Half(Formula numerator) => Seq(Frac, Grp(numerator), Grp(D(2)));
    private static Formula Squares() => Seq(Naturals(), F.Times, Naturals());
    private static Formula L1(Formula p, Formula q) =>
        Add(Call("dist", Sub(p, 1), Sub(q, 1)), Call("dist", Sub(p, 2), Sub(q, 2)));

    private static Formula DominoFormula()
    {
        Formula r = F.Id("r"), c = F.Id("c"), s = F.Id("s"), p = F.Id("p"), q = F.Id("q");
        Formula pair = Seq(OpenBrace, p, Comma, Sp, q, CloseBrace);
        Formula body = And(Equal(s, pair), And(Less(Sub(p, 1), r), And(Less(Sub(p, 2), c),
            And(Less(Sub(q, 1), r), And(Less(Sub(q, 2), c), Equal(L1(p, q), D(1)))))));
        return Disp(Iff(Call("IsDomino", r, c, s), Ex("p", Squares(), Ex("q", Squares(), body))));
    }

    private static Formula NonBondingFormula()
    {
        Formula s = F.Id("s"), t = F.Id("t"), p = F.Id("p"), q = F.Id("q");
        return Disp(Iff(Call("NonBonding", s, t),
            All("p", s, All("q", t, AtMost(D(2), L1(p, q))))));
    }

    private static Formula CountFormula()
    {
        Formula r = F.Id("r"), c = F.Id("c"), bigP = F.Id("P"), s = F.Id("s"), t = F.Id("t");
        Formula condition = And(Equal(new Formula.Absolute(bigP), D(2)),
            And(All("s", bigP, Call("IsDomino", r, c, s)),
                All("s", bigP, All("t", bigP, Implies(NotEqual(s, t), Call("NonBonding", s, t))))));
        return Disp(Equal(Call("D2", r, c),
            new Formula.Absolute(Seq(OpenBrace, bigP, Sp, Mid, Sp, condition, CloseBrace))));
    }

    private static Formula ClaimFormula()
    {
        Formula r = F.Id("r"), c = F.Id("c");
        Formula t1 = Times(Times(D(2), Square(c)), Square(r));
        Formula t2 = Times(D(2), Parenthesized(Add(Times(c, Square(r)), Times(Square(c), r))));
        Formula t3 = Times(Half(D(1)), Parenthesized(Add(Square(r), Square(c))));
        Formula t4 = Times(Times(D(2, 2), c), r);
        Formula t5 = Times(Half(D(5, 9)), Parenthesized(Add(c, r)));
        Formula poly = Subtract(Add(Subtract(Add(Subtract(t1, t2), t3), t4), t5), D(3, 0));
        return Disp(Iff(F.Id("claim"), All("r", Naturals(), All("c", Naturals(),
            Implies(AtMost(D(3), r), Implies(AtMost(D(3), c), Equal(Call("D2", r, c), poly)))))));
    }
}
