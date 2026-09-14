using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class RatajczakGcdSumParityCharacterizationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ArithSums/RatajczakGcdSumParityCharacterization.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/sloane2017a008590");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both of Ratajczak's gcd-filtered sums are even exactly at multiples of eight above one.",
        H("Ratajczak's A008590 gcd-filtered sum characterization"),
        Blocks(
            Node(
                "gcd2",
                "The second greatest common divisor",
                GcdTwoFormula(),
                "For a non-coprime pair, gcd_2 is the greatest proper divisor of the "
                    + "greatest common divisor. The slash denotes natural-number division.",
                DescribeRole.Definition),
            Node(
                "lcd2",
                "The second least common divisor",
                LcdTwoFormula(),
                "For a non-coprime pair, lcd_2 is the least divisor greater than one "
                    + "of the greatest common divisor.",
                DescribeRole.Definition),
            Node(
                "G",
                "The gcd_2-filtered sum",
                GFormula(),
                "The sum ranges from one through m and retains exactly the indices k "
                    + "that are not coprime to m. Each retained term is gcd_2(k,m).",
                DescribeRole.Definition),
            Node(
                "L",
                "The lcd_2-filtered sum",
                LFormula(),
                "The sum has the same gcd filter as G and replaces each term by "
                    + "lcd_2(k,m).",
                DescribeRole.Definition),
            Node(
                "result",
                "The simultaneous parity classification",
                ResultFormula(),
                "The gcd-filtered involution parity lemma pairs k with m-k and "
                    + "isolates m/2 as the only possible fixed point. The resulting "
                    + "modulo-four classification proves that both sums are even "
                    + "exactly when eight divides m. At m=1 both filtered sums are "
                    + "empty and even, so the hypothesis excludes that boundary.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a008590-gcd-sum-parity-characterization"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string name,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a008590-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name),
        H(title),
        StatementSource.FromAuthor(formula),
        role is DescribeRole.Definition
            ? AssessedProvenance.FromLiterature(Source)
            : AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))),
        role,
        claim);

    private static Formula GcdTwoFormula()
    {
        var k = F.Id("k");
        var m = F.Id("m");
        var gcd = Call("gcd", k, m);
        return Universal(["k", "m"], Equal(
            GcdTwo(k, m),
            Seq(gcd, Sp, Slash, Sp, Call("lpf", gcd))));
    }

    private static Formula LcdTwoFormula()
    {
        var k = F.Id("k");
        var m = F.Id("m");
        return Universal(["k", "m"], Equal(
            LcdTwo(k, m),
            Call("lpf", Call("gcd", k, m))));
    }

    private static Formula GFormula()
    {
        var k = F.Id("k");
        var m = F.Id("m");
        return Universal(["m"], Equal(
            Call("G", m),
            FilteredSum(k, m, GcdTwo(k, m))));
    }

    private static Formula LFormula()
    {
        var k = F.Id("k");
        var m = F.Id("m");
        return Universal(["m"], Equal(
            Call("L", m),
            FilteredSum(k, m, LcdTwo(k, m))));
    }

    private static Formula ResultFormula()
    {
        var m = F.Id("m");
        var simultaneousParity = new Formula.Logic(
            Parenthesized(Call("Even", Call("G", m))),
            FormulaLogicOperator.And,
            Parenthesized(Call("Even", Call("L", m))));
        var classification = new Formula.Logic(
            Parenthesized(simultaneousParity),
            FormulaLogicOperator.Iff,
            Parenthesized(Divides(D(8), m)));
        return Universal(["m"], new Formula.Logic(
            Parenthesized(Greater(m, D(1))),
            FormulaLogicOperator.Implies,
            Parenthesized(classification)));
    }

    private static Formula FilteredSum(Formula k, Formula m, Formula summand)
    {
        var interval = Seq(OpenBracket, D(1), Comma, Sp, m, CloseBracket);
        var filtered = Seq(
            OpenBrace, k, Sp, InMacro, Sp, interval, Sp, Mid, Sp,
            NotEqual(Call("gcd", k, m), D(1)), CloseBrace);
        return Seq(
            new Formula.Subscript(Sum, Seq(k, Sp, InMacro, Sp, filtered)),
            Sp,
            summand);
    }

    private static Formula GcdTwo(params Formula[] arguments) =>
        new Formula.Apply(
            Seq(Operatorname, Grp(F.Id("gcd")), Underscore, Grp(D(2))),
            [.. arguments]);

    private static Formula LcdTwo(params Formula[] arguments) =>
        new Formula.Apply(
            Seq(Operatorname, Grp(F.Id("lcd")), Underscore, Grp(D(2))),
            [.. arguments]);

    private static Formula Universal(string[] names, Formula body) => Disp(
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(
                FormulaIdentifier.Create(name), Naturals()))],
            body));

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Greater(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThan, right);

    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);
}
