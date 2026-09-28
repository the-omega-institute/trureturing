using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.CellularAutomata;

internal sealed class Rule54RowsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/CellularAutomata/Rule54Rows.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/price2015rule54rows");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The elementary cellular automaton with Wolfram rule 54, started from a single ON cell at the origin, has its centre column (OEIS A259661), its rows read as decimal digits (A118109) and its running total of ON cells (A265225) satisfying the recurrences and generating functions conjectured by Colin Barker, the floor formula conjectured by Karl V. Keller, Jr. for A118109, and the closed forms conjectured by Barker and by Wesley Ivan Hurt for A265225. Rule 54 is the elementary rule behind the interacting integrable reversible cellular automaton of Bobenko, Bordemann, Gunn and Pinkall, here applied to every cell at once.",
        H("Centre column, rows and ON cells of the Rule 54 cellular automaton"),
        Blocks(
            Node("rule", "Rule 54", RuleFormula(),
                "The new state of a cell whose left neighbour, own state and right neighbour are l, c, r is bit 4l + 2c + r of 54, the Wolfram numbering; toNat sends false and true to 0 and 1.",
                "rule54", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("cell", "Rows from a single ON cell", CellFormula(),
                "Row 0 has exactly the cell at the origin ON, and every cell of the integers is updated from its three neighbours at every step; since 000 goes to 0 the cells far from the origin stay OFF.",
                "cell", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("centre", "The sequence A259661", CentreFormula(),
                "The centre cells of rows 0, ..., n are read as decimal digits, row 0 most significant: the binary representation of the middle column.",
                "centreColumn", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("row", "The sequence A118109", RowFormula(),
                "The cells -n, ..., n of row n are read as decimal digits, the cell at -n most significant: the binary representation of the n-th iteration, with n and j cast to the integers.",
                "binaryRow", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("total", "The sequence A265225", TotalFormula(),
                "The number of ON cells of rows 0, ..., n together; each row has finitely many ON cells, and the count of a set of integers is its cardinality (Set.ncard).",
                "totalOn", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjectures of Barker, Keller and Hurt", ClaimFormula(),
                "Barker's recurrences and generating functions for the three sequences; Keller's floor formula for A118109, with natural-number division; Barker's closed form for A265225 read in the rationals and Hurt's closed form with natural-number division. Each denominator has constant term 1, so each generating function is stated as the product of the series with its denominator in the integer power series.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the conjectures", Disp(F.Id("claim")),
                "By induction on n, the cell at x of row n is ON exactly when |x| is at most n and x is congruent to n modulo 4 for even n, or x is not congruent to n + 1 modulo 4 for odd n: the rule table sends 100, 101, 001 and 010 to 1 and the other four neighbourhoods to 0. Hence the centre cell of row k is ON exactly when k is 0 or 1 modulo 4, so the centre column satisfies a(n+1) = 10 a(n) + c(n+1) with a period-4 digit c whose alternating sum over four consecutive steps vanishes, which gives its recurrence. The same invariant shows that digit j + 4 of row n + 2 equals digit j of row n and that the first four digits of row n + 2 are 1, 0, 0, 0 for even n and 1, 1, 1, 0 for odd n; reading the digits in base b, the value of row n + 2 is 1 or 1 + b + b^2 plus b^4 times the value of row n. For b = 10 this gives 9999 a(n) = 10000 * 100^n - 1 for even n and 11100 * 100^n - 111 for odd n, hence Keller's floor formula and Barker's recurrence for A118109. Every ON cell of row k lies in [-k, k], so with b = 1 the ON cells of row k number k/2 + 1 for even k and 3(k + 1)/2 for odd k; summing gives Hurt's formula, which equals Barker's closed form, and each is annihilated by (1 - x)^3 (1 + x)^2. The generating functions follow by comparing coefficients: from x^5 on they vanish by the recurrences, and the first five come from the values 1, 11, 110, 1100, 11001; 1, 111, 10001, 1110111, 100010001; and 1, 4, 6, 12, 15.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a259661-rule54-barker-keller-hurt"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("rule54-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Integers() => new Formula.Integers();
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula AsInt(Formula value) => Seq(Open, value, Colon, Sp, Integers(), Close);
    private static Formula AsRat(Formula value) => Seq(Open, value, Colon, Sp, Rationals(), Close);
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
    private static Formula NatDiv(Formula left, Formula right) =>
        Seq(left, Sp, Named("div"), Sp, right);
    private static Formula SumOver(string index, Formula range, Formula term) =>
        Seq(Sum, Underscore, Grp(F.Id(index), InMacro, range), Sp, term);

    private static Formula RuleFormula()
    {
        Formula l = F.Id("l"), c = F.Id("c"), r = F.Id("r");
        Formula index = Add(Add(Times(D(4), ToNat(l)), Times(D(2), ToNat(c))), ToNat(r));
        return Disp(Equal(Call("rule54", l, c, r), Call("testBit", D(5, 4), index)));
    }

    private static Formula CellFormula()
    {
        Formula n = F.Id("n"), x = F.Id("x");
        Formula start = Equal(Call("cell", D(0), x), Call("decide", Equal(x, D(0))));
        Formula step = Equal(Call("cell", Add(n, D(1)), x),
            Call("rule54", Call("cell", n, Subtract(x, D(1))), Call("cell", n, x),
                Call("cell", n, Add(x, D(1)))));
        return Disp(All("n", Naturals(), All("x", Integers(), And(start, step))));
    }

    private static Formula CentreFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k");
        Formula term = Times(ToNat(Call("cell", k, D(0))), Pow(D(1, 0), Subtract(n, k)));
        return Disp(Equal(Call("centreColumn", n),
            SumOver("k", Call("range", Add(n, D(1))), term)));
    }

    private static Formula RowFormula()
    {
        Formula n = F.Id("n"), j = F.Id("j");
        Formula term = Times(ToNat(Call("cell", n, Subtract(AsInt(n), AsInt(j)))), Pow(D(1, 0), j));
        return Disp(Equal(Call("binaryRow", n),
            SumOver("j", Call("range", Add(Times(D(2), n), D(1))), term)));
    }

    private static Formula TotalFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k"), x = F.Id("x");
        Formula ons = new Formula.Absolute(Seq(OpenBrace, x, InMacro, Integers(), Sp, Mid, Sp,
            Equal(Call("cell", k, x), Named("true")), CloseBrace));
        return Disp(Equal(Call("totalOn", n), SumOver("k", Call("range", Add(n, D(1))), ons)));
    }

    private static Formula Value(string name, Formula index) => AsInt(Call(name, index));

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), bigX = F.Id("X");
        Formula centreRec = All("n", Naturals(), Implies(Less(D(3), n), Equal(Value("centreColumn", n),
            Subtract(Add(Subtract(Times(D(1, 1), Value("centreColumn", Subtract(n, D(1)))),
                Times(D(1, 1), Value("centreColumn", Subtract(n, D(2))))),
                Times(D(1, 1), Value("centreColumn", Subtract(n, D(3))))),
                Times(D(1, 0), Value("centreColumn", Subtract(n, D(4))))))));
        Formula centreGf = Equal(Times(Call("mk", Seq(n, Sp, Mapsto, Sp, Value("centreColumn", n))),
            Parenthesized(Seq(Parenthesized(Subtract(D(1), bigX)),
                Parenthesized(Subtract(D(1), Times(D(1, 0), bigX))),
                Parenthesized(Add(D(1), Pow(bigX, D(2))))))), D(1));
        Formula rowRec = All("n", Naturals(), Implies(Less(D(3), n), Equal(Value("binaryRow", n),
            Subtract(Times(D(1, 0, 0, 0, 1), Value("binaryRow", Subtract(n, D(2)))),
                Times(D(1, 0, 0, 0, 0), Value("binaryRow", Subtract(n, D(4))))))));
        Formula rowGf = Equal(Times(Call("mk", Seq(n, Sp, Mapsto, Sp, Value("binaryRow", n))),
            Parenthesized(Seq(Parenthesized(Subtract(D(1), bigX)), Parenthesized(Add(D(1), bigX)),
                Parenthesized(Subtract(D(1), Times(D(1, 0, 0), bigX))),
                Parenthesized(Add(D(1), Times(D(1, 0, 0), bigX)))))),
            Add(D(1), Times(D(1, 1, 1), bigX)));
        Formula keller = All("n", Naturals(), Equal(Call("binaryRow", n),
            NatDiv(Times(Parenthesized(Add(D(1, 0, 0, 0, 0),
                Times(D(1, 1, 0, 0), Parenthesized(Seq(n, Sp, Named("mod"), Sp, D(2)))))),
                Pow(D(1, 0, 0), n)), D(9, 9, 9, 9))));
        Formula barker = All("n", Naturals(), Equal(AsRat(Call("totalOn", n)),
            Seq(Frac, Grp(Times(Parenthesized(Add(n, D(1))), Parenthesized(Add(Subtract(
                Times(D(2), n), Pow(Parenthesized(Seq(Minus, D(1))), n)), D(5))))), Grp(D(4)))));
        Formula totalRec = All("n", Naturals(), Implies(Less(D(4), n), Equal(Value("totalOn", n),
            Add(Subtract(Subtract(Add(Value("totalOn", Subtract(n, D(1))),
                Times(D(2), Value("totalOn", Subtract(n, D(2))))),
                Times(D(2), Value("totalOn", Subtract(n, D(3))))),
                Value("totalOn", Subtract(n, D(4)))), Value("totalOn", Subtract(n, D(5)))))));
        Formula totalGf = Equal(Times(Call("mk", Seq(n, Sp, Mapsto, Sp, Value("totalOn", n))),
            Parenthesized(Seq(Pow(Parenthesized(Subtract(D(1), bigX)), D(3)),
                Pow(Parenthesized(Add(D(1), bigX)), D(2))))), Add(D(1), Times(D(3), bigX)));
        Formula hurt = All("n", Naturals(), Equal(Call("totalOn", n),
            Add(Add(n, D(1)), Times(Parenthesized(Add(n, D(1))),
                Parenthesized(NatDiv(Parenthesized(Add(n, D(1))), D(2)))))));
        return Disp(Iff(F.Id("claim"), And(centreRec, And(centreGf, And(rowRec, And(rowGf,
            And(keller, And(barker, And(totalRec, And(totalGf, hurt))))))))));
    }
}
