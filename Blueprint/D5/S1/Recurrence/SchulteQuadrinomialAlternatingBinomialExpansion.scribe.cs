using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class SchulteQuadrinomialAlternatingBinomialExpansionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/SchulteQuadrinomialAlternatingBinomialExpansion.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/schulte2015a008287");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Schulte's conjectured A008287 alternating-binomial expansion is proved.",
        H("Schulte's quadrinomial alternating-binomial expansion"),
        Blocks(
            Paragraph(Text(
                "The symbols ℕ and ℤ denote the naturals (including zero) and integers; "
                    + "ℤ[X] is the integer polynomial ring in X. The indices n, k, and j "
                    + "are natural numbers, and T(n,k) is an integer. The operator "
                    + "coeff(P,k) extracts the coefficient of X^k in P; binom(a,b) "
                    + "is the natural binomial coefficient, and intCast maps its "
                    + "natural value to ℤ. Powers of −2 and the entire sum are in ℤ. "
                    + "All index subtractions, including 3n−2j and k−j, are truncated "
                    + "natural subtraction; binom(n,j)=0 when j>n. The sum over "
                    + "Finset.range(k+1) has exactly the indices j=0,...,k. "
                    + "The scope is only Schulte's 2015 A008287 conjectured %F formula; "
                    + "the Shevelev 2010 and Bala 2013 formulas are different and are "
                    + "not asserted. The proof shape is bind-only under the "
                    + "open-problem-resolution basis: factorisation, the binomial "
                    + "theorem, and coefficient extraction normalize to this expansion.")),
            Node(
                "T",
                "The quadrinomial coefficient T(n,k)",
                DefinitionFormula(),
                "For each pair of natural indices, T(n,k) extracts degree k "
                    + "from the n-th power of 1+X+X²+X³ in ℤ[X].",
                DescribeRole.Definition),
            Node(
                "result",
                "Schulte's alternating-binomial identity",
                ResultFormula(),
                "For every n and k with k≤3n, T(n,k) equals the finite integer "
                    + "sum with natural binomial coefficients cast into ℤ. The "
                    + "factorisation 1+X+X²+X³=(1+X)³−2X(1+X), the binomial "
                    + "theorem, coefficient extraction, and range reindexing give "
                    + "the identity. The proof shape is bind-only; the named open "
                    + "problem is settled under issue #8204 without an escape witness.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a008287-schulte-quadrinomial-alternating-binomial"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string name,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a008287-" + name.ToLowerInvariant()),
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

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Polynomial() => Add(
        Add(Add(D(1), F.Id("X")), Power(F.Id("X"), D(2))),
        Power(F.Id("X"), D(3)));

    private static Formula Coeff(Formula polynomial, Formula degree) =>
        Call("coeff", polynomial, degree);

    private static Formula IntCast(Formula value) => Call("intCast", value);

    private static Formula Binom(Formula upper, Formula lower) =>
        Call("binom", upper, lower);

    private static Formula FiniteSum(Formula index, Formula upper, Formula summand) =>
        Seq(new Formula.Subscript(F.Sum, Equal(index, D(0))),
            Caret, Grp(upper), Sp, summand);

    private static Formula DefinitionFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("n"), Naturals()),
                new Formula.BoundVariable(FormulaIdentifier.Create("k"), Naturals()),
            ],
            Equal(Call("T", n, k), Coeff(Power(Parenthesized(Polynomial()), n), k))));
    }

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var j = F.Id("j");
        var summand = Multiply(
            Multiply(
                Power(Parenthesized(Seq(Minus, D(2))), j),
                IntCast(Binom(n, j))),
            IntCast(Binom(
                Subtract(Multiply(D(3), n), Multiply(D(2), j)),
                Subtract(k, j))));
        var equality = Equal(Call("T", n, k), FiniteSum(j, k, summand));
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("n"), Naturals()),
                new Formula.BoundVariable(FormulaIdentifier.Create("k"), Naturals()),
            ],
            new Formula.Logic(
                Parenthesized(new Formula.Relation(
                    k, FormulaRelationOperator.LessThanOrEqual,
                    Multiply(D(3), n))),
                FormulaLogicOperator.Implies,
                Parenthesized(equality))));
    }
}
