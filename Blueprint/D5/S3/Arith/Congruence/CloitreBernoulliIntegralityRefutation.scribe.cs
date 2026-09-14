using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class CloitreBernoulliIntegralityRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/CloitreBernoulliIntegralityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/cloitre2004a090825");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The integer 833 refutes Cloitre's Bernoulli-integrality conjecture for A090825.",
        H("The OEIS A090825 Bernoulli-Integrality Conjecture"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a090825-rational-expression"),
                DeclarationHandle.Create(Prefix + "F"),
                H("The rational expression defining A090825"),
                StatementSource.FromAuthor(FFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Every factor is multiplied in the rationals. Here B(2n) is the "
                        + "Bernoulli number with even index 2n, while 3/2 and 1/n are "
                        + "rational quotients."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a053176-prime-factor-condition"),
                DeclarationHandle.Create(Prefix + "A053176"),
                H("The prime sequence A053176"),
                StatementSource.FromAuthor(A053176Formula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A natural p lies in A053176 exactly when p is prime and 2p+1 is "
                        + "not prime."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a090825-cloitre-integrality-conjecture"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Cloitre's composite-factor integrality conjecture"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every composite natural n greater than one, the conjecture "
                        + "asserts that F(n) is an integer whenever each prime divisor of n "
                        + "belongs to A053176."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a090825-cloitre-integrality-conjecture-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The conjecture fails at n = 833"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The integer 833 has prime factors 7 and 17, both in A053176. The "
                        + "von Staudt-Clausen theorem gives the Bernoulli factor valuation "
                        + "minus one at 239, while every other factor has valuation zero. "
                        + "Thus F(833) is not an integer. The separate prime congruence "
                        + "clause and the subsequence question are untouched."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a090825-bernoulli-integrality-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula FFormula()
    {
        var n = F.Id("n");
        var expression = Multiply(
            Fraction(D(3), D(2)),
            Multiply(
                Fraction(D(1), n),
                Multiply(
                    Add(Multiply(D(2), n), D(1)),
                    Multiply(
                        Add(Power(D(3), n), D(1)),
                        Call("B", Multiply(D(2), n))))));
        return Disp(ForAll([Bound("n", Naturals())],
            Equal(Call("F", n), expression)));
    }

    private static Formula A053176Formula()
    {
        var p = F.Id("p");
        var condition = And(
            Prime(p),
            new Formula.Not(Prime(Add(Multiply(D(2), p), D(1)))));
        return Disp(ForAll([Bound("p", Naturals())],
            Iff(Call("A053176", p), condition)));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var p = F.Id("p");
        var z = F.Id("z");
        var everyPrimeFactor = ForAll([Bound("p", Naturals())],
            Implies(
                Prime(p),
                Implies(
                    Divides(p, n),
                    Call("A053176", p))));
        var integerValue = Exists([Bound("z", Integers())],
            Equal(Call("F", n), Coerce(z, Rationals())));
        var body = ForAll([Bound("n", Naturals())],
            Implies(
                Less(D(1), n),
                Implies(
                    new Formula.Not(Prime(n)),
                    Implies(everyPrimeFactor, integerValue))));
        return Disp(Iff(F.Id("claim"), body));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula.BoundVariable Bound(string name, Formula domain) => new(
        FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Rationals() =>
        Seq(Mathbb, new Formula.LatexGroup([F.Id("Q")]));

    private static Formula Integers() => new Formula.Integers();

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Prime(Formula value) => Call("Prime", value);

    private static Formula Coerce(Formula value, Formula type) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, type));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And,
            Parenthesized(right));

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff,
            Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies,
            Parenthesized(right));
}
