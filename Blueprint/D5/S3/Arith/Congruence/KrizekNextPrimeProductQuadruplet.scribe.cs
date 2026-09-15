using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class KrizekNextPrimeProductQuadrupletDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/KrizekNextPrimeProductQuadruplet.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/smith2017a136162");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Krizek's next-prime product has four prime neighbors at offsets two and four exactly when the prime input is three.",
        H("Krizek's Next-Prime Product Quadruplet"),
        Blocks(
            Node("nextPrime", "The next-prime function", NextPrimeFormula(),
                "For each natural q, nextPrime(q) is Mathlib's Nat.find applied to the "
                    + "infinitude of primes. It is the least prime greater than or equal "
                    + "to q+1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Q", "The next-prime product", QFormula(),
                "For each natural q, Q(q) is the product of q and nextPrime(q).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The unique prime input", ResultFormula(),
                "For a prime q, the four natural numbers Q(q)-4, Q(q)-2, Q(q)+2, "
                    + "and Q(q)+4 are all prime exactly when q=3. Subtraction here is "
                    + "truncated natural-number subtraction. For q at least five, q and "
                    + "nextPrime(q) are nonzero modulo three, so their product has residue "
                    + "one or two; respectively Q(q)+2 or Q(q)-2 is then a multiple of "
                    + "three greater than three. The cases q=2 and q=3 reduce to the "
                    + "explicit values 4 and the prime quadruplet 11, 13, 17, 19.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a136162-krizek-next-prime-product-quadruplet"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a136162-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula NextPrimeFormula()
    {
        var q = F.Id("q");
        var x = F.Id("x");
        var conditions = And(
            LessOrEqual(Add(q, D(1)), x),
            Prime(x));
        var candidates = Seq(
            OpenBrace, x, Sp, InMacro, Sp, Naturals(), Sp, Mid, Sp,
            Parenthesized(conditions), CloseBrace);
        return Disp(Universal("q", Equal(
            Call("nextPrime", q), Call("sInf", candidates))));
    }

    private static Formula QFormula()
    {
        var q = F.Id("q");
        return Disp(Universal("q", Equal(
            Call("Q", q), Multiply(q, Call("nextPrime", q)))));
    }

    private static Formula ResultFormula()
    {
        var q = F.Id("q");
        var product = Call("Q", q);
        var primeNeighbors = And(
            Prime(Subtract(product, D(4))),
            And(
                Prime(Subtract(product, D(2))),
                And(
                    Prime(Add(product, D(2))),
                    Prime(Add(product, D(4))))));
        var characterization = Iff(
            Parenthesized(primeNeighbors),
            Equal(q, D(3)));
        return Disp(Universal("q", Implies(
            Prime(q), Parenthesized(characterization))));
    }

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Universal(string name, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(name),
            Naturals(),
            body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Prime(Formula value) => Call("Prime", value);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
