using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class KrizekAllMultiplesOfTheOrderDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/KrizekAllMultiplesOfTheOrder.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/hasler2016a260407");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Krizek's A260407 condition at exponent n-1 is equivalent to the condition at every positive multiple of that exponent.",
        H("Krizek's A260407 Divisibility at Every Positive Multiple"),
        Blocks(
            Node("modulus", "The A260407 modulus", ModulusFormula(),
                "For each natural n, modulus(n) is (n-1) squared plus one. The subtraction "
                    + "is truncated natural-number subtraction.",
                "modulus", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("in-sequence", "The A260407 membership condition", InSequenceFormula(),
                "For each natural n, inSequence(n) holds exactly when modulus(n) divides "
                    + "2 raised to n-1, minus one. Both subtractions are truncated "
                    + "natural-number subtraction.",
                "inSequence", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("all-multiples", "Divisibility at every positive multiple", AllMultiplesFormula(),
                "For each natural n, allMultiples(n) holds exactly when every positive "
                    + "natural k gives divisibility at exponent k times n-1.",
                "allMultiples", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("result", "Equivalence of the two conditions", ResultFormula(),
                "For every natural n at least one, the A260407 membership condition is "
                    + "equivalent to divisibility at every positive multiple of n-1. "
                    + "The forward implication applies the textbook fact that a power "
                    + "minus one divides the corresponding power at a multiple exponent. "
                    + "The converse takes k equal to one. At n equal to one, modulus(n) "
                    + "is one and both divisibility statements hold.",
                "result", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a260407-krizek-all-multiples-of-the-order"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string id,
        string title,
        Formula formula,
        string prose,
        string declaration,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("a260407-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula ModulusFormula()
    {
        var n = F.Id("n");
        var shifted = Parenthesized(Subtract(n, D(1)));
        return Disp(Universal("n", Equal(
            Call("modulus", n), Add(Power(shifted, D(2)), D(1)))));
    }

    private static Formula InSequenceFormula()
    {
        var n = F.Id("n");
        var exponent = Parenthesized(Subtract(n, D(1)));
        var powerMinusOne = Subtract(Power(D(2), exponent), D(1));
        return Disp(Universal("n", Iff(
            Call("inSequence", n), Divides(Call("modulus", n), powerMinusOne))));
    }

    private static Formula AllMultiplesFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var exponent = Parenthesized(Multiply(k, Parenthesized(Subtract(n, D(1)))));
        var divisibility = Divides(
            Call("modulus", n), Subtract(Power(D(2), exponent), D(1)));
        var everyPositiveMultiple = Universal("k", Implies(
            LessOrEqual(D(1), k), divisibility));
        return Disp(Universal("n", Iff(
            Call("allMultiples", n), everyPositiveMultiple)));
    }

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        return Disp(Universal("n", Implies(
            LessOrEqual(D(1), n),
            Iff(Call("inSequence", n), Call("allMultiples", n)))));
    }

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Universal(string variable, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable),
            Naturals(),
            body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
