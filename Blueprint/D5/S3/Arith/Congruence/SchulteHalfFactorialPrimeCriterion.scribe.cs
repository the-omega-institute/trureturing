using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class SchulteHalfFactorialPrimeCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/SchulteHalfFactorialPrimeCriterion.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/schulte2025a000680");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Schulte's A000680 half-factorial sequence satisfies his primality criterion.",
        H("Schulte's A000680 half-factorial primality criterion"),
        Blocks(
            Paragraph(Text(
                "All variables range over the natural numbers N, including zero. "
                    + "The index is n, a(n) is the A000680 value, factorial is the "
                    + "natural factorial, powers and multiplication are natural-number "
                    + "operations, and the slash denotes exact natural-number division, "
                    + "not a fraction. Prime(x) means that x is prime, and u divides v "
                    + "is the natural divisibility relation. The scope is exactly the "
                    + "OEIS Conjecture sentence: for every n greater than zero, the "
                    + "displayed divisibility is equivalent to primality of 2n+1. The "
                    + "odd-composite factorial divisibility used in the proof is the "
                    + "frozen LaymanOddPowerFactorialResidue theorem, reused here.")),
            Node(
                "a",
                "The A000680 half-factorial sequence",
                DefinitionFormula(),
                "The sequence value is the exact natural-number quotient of the "
                    + "factorial of 2n by 2 raised to n.",
                DescribeRole.Definition),
            Node(
                "result",
                "Schulte's primality criterion",
                ResultFormula(),
                "For every positive natural index, the odd number 2n+1 divides "
                    + "a(n)+2^n exactly when that odd number is prime. The proof "
                    + "uses Wilson's theorem and Fermat's theorem in the prime branch, "
                    + "and the frozen odd-composite factorial divisibility theorem in "
                    + "the converse branch.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a000680-schulte-half-factorial-prime-criterion"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string name,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a000680-" + name),
        DeclarationHandle.Create(Prefix + name),
        H(title),
        StatementSource.FromAuthor(formula),
        AssessedProvenance.FromLiterature(Source),
        Blocks(Paragraph(Text(prose))),
        role,
        claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Power(Formula baseValue, Formula exponent) =>
        new Formula.Power(baseValue, exponent);

    private static Formula Twice(Formula value) => Multiply(D(2), value);

    private static Formula OddIndex(Formula n) => Add(Twice(n), D(1));

    private static Formula Quotient(Formula numerator, Formula denominator) =>
        Seq(Parenthesized(numerator), Sp, Slash, Sp, Parenthesized(denominator));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);

    private static Formula DefinitionFormula()
    {
        var n = F.Id("n");
        var factorial = Call("factorial", Twice(n));
        var quotient = Quotient(factorial, Power(D(2), n));
        return Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            Naturals(),
            Equal(Call("a", n), quotient)));
    }

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var divisibility = Divides(
            OddIndex(n),
            Add(Call("a", n), Power(D(2), n)));
        var primality = Call("Prime", OddIndex(n));
        var criterion = new Formula.Logic(
            Parenthesized(divisibility),
            FormulaLogicOperator.Iff,
            Parenthesized(primality));
        var implication = new Formula.Logic(
            Parenthesized(Less(D(0), n)),
            FormulaLogicOperator.Implies,
            Parenthesized(criterion));
        return Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            Naturals(),
            implication));
    }
}
