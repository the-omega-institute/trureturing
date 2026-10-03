using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.CellularAutomata;

internal sealed class Rule201RowsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/CellularAutomata/Rule201Rows.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/price2016rule201rows");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The elementary cellular automaton with Wolfram rule 201, started from a single ON cell at the origin and updated at every cell of the integers, has row n read on the cells -n, ..., n equal to 2 * 4^n - (2 [n odd] + 5 [n > 0]) * 2^(n-1) - 1 in base 2, as conjectured by M. F. Hasler for OEIS A267681; both the base-2 reading (A267681) and the decimal-digit reading (A267680) satisfy the order-4 recurrences and generating functions conjectured by Colin Barker. Rule 201 is the local update rule of the Floquet-PXP cellular automaton, here applied to every cell at once.",
        H("Rows of the Rule 201 cellular automaton"),
        Blocks(
            Node("rule", "Rule 201", RuleFormula(),
                "The new state of a cell whose left neighbour, own state and right neighbour are l, c, r is bit 4l + 2c + r of 201, the Wolfram numbering; toNat sends false and true to 0 and 1.",
                "rule201", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("cell", "Rows from a single ON cell", CellFormula(),
                "Row 0 has exactly the cell at the origin ON, and every cell of the integers is updated from its three neighbours at every step, so cells far from the origin follow the background: 000 goes to 1 under rule 201.",
                "cell", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("window", "The window of row n", WindowFormula(),
                "The cells -n, ..., n of row n are read as digits in base b, the cell at -n most significant; the cell at n - j carries weight b^j, with n and j cast to the integers.",
                "windowValue", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("decimal", "The sequence A267681", Reading("decimalRepresentation", D(2)),
                "A267681, the decimal representation of the n-th iteration: the window read as a binary number.",
                "decimalRepresentation", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("binary", "The sequence A267680", Reading("binaryRepresentation", D(1, 0)),
                "A267680, the binary representation of the n-th iteration: the window read as a string of decimal digits.",
                "binaryRepresentation", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjectures of Barker and Hasler", ClaimFormula(),
                "Hasler's closed form for A267681, with [n odd] = n mod 2 and [0 < n] the value of if 0 < n then 1 else 0; Barker's recurrences for n > 4 and his generating functions for both sequences. Each denominator has constant term 1, so the generating function is stated as the product of the series with its denominator; all values are cast to the integers.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the conjectures", Disp(F.Id("claim")),
                "By induction on n, every row n at least 1 has the cell at x ON exactly when |x| is at least 2, or x = 0 and n is even: the rule table sends 111, 011 and 110 to 1, keeps the cells at x = -1 and x = 1 off through 001, 101 and 100, and flips the centre through 000 to 1 and 010 to 0; row 1 comes from row 0 through 000, 001, 100 and 010. Hence the window of row n at least 1 in base b is the geometric sum of b^j for j < 2n + 1 minus b^(n+1), b^(n-1) and, for odd n, b^n. With (b - 1) times the geometric sum equal to b^(2n+1) - 1 and 2 [n odd] = 1 - (-1)^n, for every base b at least 1, twice (b - 1) times the window is a fixed combination of b^(2n), b^n, (-b)^n and 1, each annihilated by (1 - x)(1 - bx)(1 + bx)(1 - b^2 x); for b = 2 and b = 10 this gives the two recurrences for n > 4, and for b = 2 the same evaluation is Hasler's formula. Comparing coefficients, the recurrence makes every coefficient of the product with the denominator vanish from x^5 on, and the first five coefficients come from the values 1, 0, 21, 99, 471 and 1, 0, 10101, 1100011, 111010111.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a267681-rule201-barker-hasler"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("rule201-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => new Formula.Integers();
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula AsInt(Formula value) => Seq(Open, value, Colon, Sp, Integers(), Close);
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
    private static Formula Iverson(Formula condition) => Seq(OpenBracket, condition, CloseBracket);

    private static Formula RuleFormula()
    {
        Formula l = F.Id("l"), c = F.Id("c"), r = F.Id("r");
        Formula index = Add(Add(Times(D(4), ToNat(l)), Times(D(2), ToNat(c))), ToNat(r));
        return Disp(Equal(Call("rule201", l, c, r), Call("testBit", D(2, 0, 1), index)));
    }

    private static Formula CellFormula()
    {
        Formula n = F.Id("n"), x = F.Id("x");
        Formula start = Equal(Call("cell", D(0), x), Call("decide", Equal(x, D(0))));
        Formula step = Equal(Call("cell", Add(n, D(1)), x),
            Call("rule201", Call("cell", n, Subtract(x, D(1))), Call("cell", n, x),
                Call("cell", n, Add(x, D(1)))));
        return Disp(All("n", Naturals(), All("x", Integers(), And(start, step))));
    }

    private static Formula WindowFormula()
    {
        Formula b = F.Id("b"), n = F.Id("n"), j = F.Id("j");
        Formula range = Call("range", Add(Times(D(2), n), D(1)));
        Formula digit = ToNat(Call("cell", n, Subtract(AsInt(n), AsInt(j))));
        return Disp(Equal(Call("windowValue", b, n),
            Seq(Sum, Underscore, Grp(j, InMacro, range), Sp, Times(digit, Pow(b, j)))));
    }

    private static Formula Reading(string name, Formula baseValue)
    {
        Formula n = F.Id("n");
        return Disp(Equal(Call(name, n), Call("windowValue", baseValue, n)));
    }

    private static Formula Recurrence(string name, Formula c1, Formula c3, Formula c4)
    {
        Formula n = F.Id("n");
        Formula value(Formula index) => AsInt(Call(name, index));
        Formula right = Add(Subtract(Times(c1, value(Subtract(n, D(1)))),
            Times(c3, value(Subtract(n, D(3))))), Times(c4, value(Subtract(n, D(4)))));
        return All("n", Naturals(), Implies(Less(D(4), n), Equal(value(n), right)));
    }

    private static Formula GeneratingFunction(
        string name, Formula b, Formula b2, Formula[] numerator)
    {
        Formula n = F.Id("n"), bigX = F.Id("X");
        Formula series = Call("mk", Seq(n, Sp, Mapsto, Sp, AsInt(Call(name, n))));
        Formula denominator = Seq(
            Parenthesized(Subtract(D(1), bigX)), Parenthesized(Subtract(D(1), Times(b, bigX))),
            Parenthesized(Add(D(1), Times(b, bigX))), Parenthesized(Subtract(D(1), Times(b2, bigX))));
        Formula poly = Subtract(Add(Add(Subtract(numerator[0], Times(numerator[1], bigX)),
            Times(numerator[2], Pow(bigX, D(2)))), Times(numerator[3], Pow(bigX, D(3)))),
            Times(numerator[4], Pow(bigX, D(4))));
        return Equal(Times(series, Parenthesized(denominator)), poly);
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n");
        Formula parity = AsInt(Seq(n, Sp, Named("mod"), Sp, D(2)));
        Formula factor = Add(Times(parity, D(2)), Times(Iverson(Less(D(0), n)), D(5)));
        Formula hasler = All("n", Naturals(), Equal(AsInt(Call("decimalRepresentation", n)),
            Subtract(Subtract(Times(D(2), Pow(D(4), n)),
                Times(Parenthesized(factor), Pow(D(2), Subtract(n, D(1))))), D(1))));
        Formula recurrence2 = Recurrence("decimalRepresentation", D(5), D(2, 0), D(1, 6));
        Formula series2 = GeneratingFunction("decimalRepresentation", D(2), D(4),
            [D(1), D(5), D(2, 1), D(1, 4), D(4, 0)]);
        Formula recurrence10 = Recurrence("binaryRepresentation", D(1, 0, 1), D(1, 0, 1, 0, 0),
            D(1, 0, 0, 0, 0));
        Formula series10 = GeneratingFunction("binaryRepresentation", D(1, 0), D(1, 0, 0),
            [D(1), D(1, 0, 1), D(1, 0, 1, 0, 1), D(8, 9, 9, 1, 0), D(1, 0, 1, 0, 0, 0)]);
        return Disp(Iff(F.Id("claim"),
            And(hasler, And(recurrence2, And(series2, And(recurrence10, series10))))));
    }
}
