using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.CellularAutomata;

internal sealed class Rule41OnCellCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/CellularAutomata/Rule41OnCellCount.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/price2016rule41oncells");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The elementary cellular automaton with Wolfram rule 41, started from a single ON cell at the origin and updated at every cell of the integers, has 1, 8k, 2 and 8k + 3 ON cells among the cells -n, ..., n of row n = 4k, 4k + 1, 4k + 2 and 4k + 3; the counts therefore satisfy Colin Barker's conjectured recurrence a(n) = a(n - 2) + a(n - 4) - a(n - 6) for n > 5 and generating function (1 + x^2 + 3x^3 - 2x^4 + 5x^5) / ((1 - x)^2 (1 + x)^2 (1 + x^2)) for OEIS A266614.",
        H("ON cells of the Rule 41 cellular automaton"),
        Blocks(
            Node("rule", "Rule 41", RuleFormula(),
                "The new state of a cell whose left neighbour, own state and right neighbour are l, c, r is bit 4l + 2c + r of 41, the Wolfram numbering; toNat sends false and true to 0 and 1.",
                "rule41", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("count", "The sequence A266614", CountFormula(),
                "A266614, the number of ON (black) cells in the n-th iteration: the cells x of row n with -n ≤ x ≤ n that are ON, with n cast to the integers. The rows are the frozen single-seed evolution row g of RuleThirtyTwentyTwoMersenneSignRefutation with g = rule41: row g 0 x is true exactly for x = 0, and row g (m + 1) x = g (row g m (x - 1)) (row g m x) (row g m (x + 1)) for every integer x, so every cell of the integers is updated at every step and cells far from the origin follow the background, which alternates because 000 goes to 1 and 111 goes to 0 under rule 41.",
                "onCount", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjectures of Barker", ClaimFormula(),
                "Barker's recurrence for n > 5 and his generating function, read in the integers, with the generating function stated as the product of the series with its denominator, which has constant term 1.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the conjectures", Disp(F.Id("claim")),
                "By induction on n, the background of row n is OFF for even n and ON for odd n, and row n differs from it exactly at {n}, {n - 2, n - 1, n}, {n - 2, n} or {n - 4, n - 3, n - 1, n} according as n is 0, 1, 2 or 3 mod 4. Rule 41 sends lcr to 1 exactly for 000, 011 and 101. From phase 0, 000 switches the background ON and the neighbourhoods 001, 010 and 100 around the ON cell n turn the cells n - 1, n and n + 1 OFF. From phase 1, 111 switches the background OFF, and around the OFF cells n - 2, n - 1, n only 000 at n - 1 and 011 at n + 1 turn ON. From phase 2, 000 switches the background ON; around the ON cells n - 2 and n the neighbourhoods 001, 010, 010 and 100 turn the cells n - 3, n - 2, n and n + 1 OFF, while 101 keeps n - 1 ON. From phase 3, 111 switches the background OFF, and around the OFF cells n - 4, n - 3, n - 1, n only 011 at n + 1 turns ON. All the exceptional cells lie in the window, so the counts are 1, 2n - 2 = 8k, 2 and 2n - 3 = 8k + 3 for n = 4k, 4k + 1, 4k + 2, 4k + 3. The recurrence follows phase by phase, and comparing coefficients, it makes every coefficient of the product with (1 - x)^2 (1 + x)^2 (1 + x^2) = 1 - x^2 - x^4 + x^6 vanish from x^6 on, while the first six coefficients come from the values 1, 0, 2, 3, 1, 8.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a266614-rule41-barker"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("rule41-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => new Formula.Integers();
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
        return Disp(Equal(Call("rule41", l, c, r), Call("testBit", D(4, 1), index)));
    }

    private static Formula CountFormula()
    {
        Formula n = F.Id("n"), x = F.Id("x");
        Formula window = Call("Icc", new Formula.Negate(As(n, Integers())), As(n, Integers()));
        Formula on = Seq(x, Sp, Mapsto, Sp, Equal(Call("row", Named("rule41"), n, x), Named("true")));
        return Disp(Equal(Call("onCount", n), Call("card", Call("filter", on, window))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), bigX = F.Id("X");
        Formula count(Formula index) => As(Call("onCount", index), Integers());
        Formula recurrence = All("n", Naturals(), Implies(Less(D(5), n),
            Equal(count(n), Subtract(Add(count(Subtract(n, D(2))), count(Subtract(n, D(4)))),
                count(Subtract(n, D(6)))))));
        Formula series = Call("mk", Seq(n, Sp, Mapsto, Sp, count(n)));
        Formula denominator = Seq(
            Pow(Parenthesized(Subtract(D(1), bigX)), D(2)),
            Pow(Parenthesized(Add(D(1), bigX)), D(2)),
            Parenthesized(Add(D(1), Pow(bigX, D(2)))));
        Formula numerator = Add(Subtract(Add(Add(D(1), Pow(bigX, D(2))),
            Times(D(3), Pow(bigX, D(3)))), Times(D(2), Pow(bigX, D(4)))),
            Times(D(5), Pow(bigX, D(5))));
        Formula generating = Equal(Times(series, Parenthesized(denominator)), numerator);
        return Disp(Iff(F.Id("claim"), And(recurrence, generating)));
    }
}
