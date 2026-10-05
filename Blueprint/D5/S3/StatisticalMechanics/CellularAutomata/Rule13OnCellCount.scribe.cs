using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.CellularAutomata;

internal sealed class Rule13OnCellCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/CellularAutomata/Rule13OnCellCount.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/price2015rule13oncells");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The elementary cellular automaton with Wolfram rule 13, started from a single ON cell at the origin and updated at every cell of the integers, has n + 1 ON cells among the cells -2n, ..., 2n of row 2n and 3n + 1 ON cells among the cells -(2n + 1), ..., 2n + 1 of row 2n + 1, as conjectured by Ctibor O. Zizka for OEIS A266285; the counts therefore satisfy Colin Barker's closed form ((-1)^n (3 - 2n) + 4n + 1) / 4, his recurrence a(n) = 2 a(n - 2) - a(n - 4) for n > 3 and his generating function (1 + x + 2x^3) / ((1 - x)^2 (1 + x)^2).",
        H("ON cells of the Rule 13 cellular automaton"),
        Blocks(
            Node("rule", "Rule 13", RuleFormula(),
                "The new state of a cell whose left neighbour, own state and right neighbour are l, c, r is bit 4l + 2c + r of 13, the Wolfram numbering; toNat sends false and true to 0 and 1.",
                "rule13", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("count", "The sequence A266285", CountFormula(),
                "A266285, the number of ON (black) cells in the n-th iteration: the cells x of row n with -n ≤ x ≤ n that are ON, with n cast to the integers. The rows are the frozen single-seed evolution row g of RuleThirtyTwentyTwoMersenneSignRefutation with g = rule13: row g 0 x is true exactly for x = 0, and row g (m + 1) x = g (row g m (x - 1)) (row g m x) (row g m (x + 1)) for every integer x, so every cell of the integers is updated at every step and cells far from the origin follow the background, which alternates because 000 goes to 1 and 111 goes to 0 under rule 13.",
                "onCount", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjectures of Barker and Zizka", ClaimFormula(),
                "Barker's closed form, read in the rationals; his recurrence for n > 3 and his generating function, read in the integers, with the generating function stated as the product of the series with its denominator, which has constant term 1; and Zizka's formulas for even and odd indices.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the conjectures", Disp(F.Id("claim")),
                "By induction on n, row 2k is ON exactly at the even x with 0 ≤ x ≤ 2k, and row 2k + 1 is OFF exactly at the odd x with -1 ≤ x ≤ 2k + 1. Rule 13 sends lcr to 1 exactly when l = 0 and either c = 1 or r = 0. From row 2k, a cell whose left neighbour is one of the ON cells 0, 2, ..., 2k turns OFF, which covers the odd x from 1 to 2k + 1; the cell -1 has an OFF left neighbour, an OFF centre and the ON right neighbour 0, so it turns OFF; every other cell has an OFF left neighbour and either an ON centre or an OFF right neighbour, so it turns ON. From row 2k + 1, a cell can turn ON only if its left neighbour is one of the OFF cells -1, 1, ..., 2k + 1, that is, x is even with 0 ≤ x ≤ 2k + 2, and each such cell has an ON centre, so it turns ON. Counting, the window of row 2k holds the k + 1 even cells from 0 to 2k, and the window of row 2k + 1, which has 4k + 3 cells, holds k + 2 OFF cells. The closed form follows by parity, the recurrence by parity of n - 4, and comparing coefficients, the recurrence makes every coefficient of the product with (1 - x)^2 (1 + x)^2 = 1 - 2x^2 + x^4 vanish from x^4 on, while the first four coefficients come from the values 1, 1, 2, 4.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a266285-rule13-barker-zizka"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("rule13-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => new Formula.Integers();
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula As(Formula value, Formula type) => Seq(Open, value, Colon, Sp, type, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
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
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula ToNat(Formula value) => Call("toNat", value);

    private static Formula RuleFormula()
    {
        Formula l = F.Id("l"), c = F.Id("c"), r = F.Id("r");
        Formula index = Add(Add(Times(D(4), ToNat(l)), Times(D(2), ToNat(c))), ToNat(r));
        return Disp(Equal(Call("rule13", l, c, r), Call("testBit", D(1, 3), index)));
    }

    private static Formula CountFormula()
    {
        Formula n = F.Id("n"), x = F.Id("x");
        Formula window = Call("Icc", new Formula.Negate(As(n, Integers())), As(n, Integers()));
        Formula on = Seq(x, Sp, Mapsto, Sp, Equal(Call("row", Named("rule13"), n, x), Named("true")));
        return Disp(Equal(Call("onCount", n), Call("card", Call("filter", on, window))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), bigX = F.Id("X");
        Formula count(Formula index, Formula type) => As(Call("onCount", index), type);
        Formula numerator = Add(Add(
            Times(Pow(Parenthesized(new Formula.Negate(D(1))), n),
                Parenthesized(Subtract(D(3), Times(D(2), n)))),
            Times(D(4), n)), D(1));
        Formula closed = All("n", Naturals(),
            Equal(count(n, Rationals()), new Formula.Fraction(numerator, D(4))));
        Formula recurrence = All("n", Naturals(), Implies(Less(D(3), n),
            Equal(count(n, Integers()), Subtract(
                Times(D(2), count(Subtract(n, D(2)), Integers())),
                count(Subtract(n, D(4)), Integers())))));
        Formula series = Call("mk", Seq(n, Sp, Mapsto, Sp, count(n, Integers())));
        Formula denominator = Seq(
            Pow(Parenthesized(Subtract(D(1), bigX)), D(2)),
            Pow(Parenthesized(Add(D(1), bigX)), D(2)));
        Formula generating = Equal(Times(series, Parenthesized(denominator)),
            Add(Add(D(1), bigX), Times(D(2), Pow(bigX, D(3)))));
        Formula even = All("n", Naturals(),
            Equal(Call("onCount", Times(D(2), n)), Add(n, D(1))));
        Formula odd = All("n", Naturals(),
            Equal(Call("onCount", Add(Times(D(2), n), D(1))), Add(Times(D(3), n), D(1))));
        return Disp(Iff(F.Id("claim"),
            And(closed, And(recurrence, And(generating, And(even, odd))))));
    }
}
