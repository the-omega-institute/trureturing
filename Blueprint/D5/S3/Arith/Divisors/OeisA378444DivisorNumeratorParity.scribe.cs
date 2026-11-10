using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors;

internal sealed class OeisA378444DivisorNumeratorParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/OeisA378444DivisorNumeratorParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PrimeForms/karttunen2025a378444");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Karttunen's A378444 divisor count equals the ceiling of half A174273.",
        H("Karttunen's divisor numerator parity identity"),
        Blocks(
            Node("r", "The rational prime-exponent sum", RFormula(),
                "OEIS A083345, NAME, revision 68 (unpaginated): “Numerator of r(n) = Sum(e/p: n=Product(p^e)); a(n) = n' / gcd(n,n'), where n' is the arithmetic derivative of n.” The function r is the displayed rational sum. Finsupp.sum ranges over the support of Nat.factorization; both casts in each quotient are to Rat. The empty sum gives r(1) = 0.",
                AssessedProvenance.FromLiterature(Source)),
            Node("A083345", "The reduced numerator", NumeratorFormula(),
                "OEIS A378444, NAME, revision 14 (unpaginated): “a(n) is the number of divisors d of n such that A083345(d) is even, where A083345(n) is the numerator of Sum(e/p: n=Product(p^e)).” Rat.num is the reduced numerator with positive denominator, including Rat.num 0 = 0.",
                AssessedProvenance.FromLiterature(Source)),
            Node("A378444", "Divisors with even numerator", CountFormula(),
                "OEIS A378444, NAME, revision 14 (unpaginated): “a(n) is the number of divisors d of n such that A083345(d) is even, where A083345(n) is the numerator of Sum(e/p: n=Product(p^e)).” For n ≥ 1, Nat.divisors contains exactly the positive divisors. In particular d = 1 is counted because its numerator is zero. The residue here is an integer residue modulo 2.",
                AssessedProvenance.FromLiterature(Source)),
            Node("A035263", "Parity of the exponent at two", IndicatorFormula(),
                "OEIS A035263, COMMENT, revision 266 (unpaginated): “a(n) is 1 if the number of trailing zeros in the binary representation of n is even.” For positive n this is the parity of Nat.factorization n 2. The residue here is a natural residue modulo 2.",
                AssessedProvenance.FromLiterature(Source)),
            Node("A174273", "The divisor transform", TransformFormula(),
                "OEIS A174273, NAME, revision 17 (unpaginated): “Inverse Moebius transform of A035263.” This is the sum of A035263 over the positive divisors for n ≥ 1.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Karttunen's ceiling conjecture", Equal(F.Id("claim"), Parenthesized(ClaimBody())),
                "OEIS A378444, FORMULA, revision 14 (unpaginated): “a(n) = ceiling(A174273(n)/2). [Conjectured] - _Antti Karttunen_, May 14 2025”. Its offset is 1. The variable n ranges over Nat with 1 ≤ n. The cast to Rat precedes division by 2; Nat.ceil equals the ordinary ceiling of this nonnegative rational.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("a378444-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The ceiling identity holds for every positive integer"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Write a divisor as 2^a times a product of odd prime powers. An odd common denominator shows that its reduced numerator is even exactly when a is even and a/2 plus the sum of the odd-prime exponents is even. Halving the even exponent at 2 identifies these divisors with exponent vectors in a finite rectangular box. The alternating sign sum of that box is a product of zeros and ones, so the number of even exponent sums is the ceiling of half its size. This includes 1, odd integers, powers of two and arbitrary mixed prime powers. The proof uses the inverse Moebius transform definition of A174273."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("karttunen-a378444"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("a378444-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula RFormula()
    {
        Formula n = F.Id("n"), p = F.Id("p"), e = F.Id("e");
        return All("n", Equal(Call("r", n), App(Qualified("Finsupp", "sum"),
            App(Qualified("Nat", "factorization"), n),
            Fun("p", Fun("e", new Formula.Fraction(Cast(e, "Rat"), Cast(p, "Rat")))))));
    }

    private static Formula NumeratorFormula()
    {
        Formula n = F.Id("n");
        return All("n", Equal(Call("A083345", n), App(Qualified("Rat", "num"), Call("r", n))));
    }

    private static Formula CountFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d");
        return All("n", Equal(Call("A378444", n), App(Qualified("Finset", "card"),
            App(Qualified("Finset", "filter"),
                Fun("d", Equal(new Formula.Modulo(Call("A083345", d), D(2)), D(0))),
                App(Qualified("Nat", "divisors"), n)))));
    }

    private static Formula IndicatorFormula()
    {
        Formula n = F.Id("n");
        return All("n", Equal(Call("A035263", n), Seq(
            F.Id("if"), Sp,
            Parenthesized(Equal(new Formula.Modulo(App(Qualified("Nat", "factorization"), n, D(2)), D(2)), D(0))),
            Sp, F.Id("then"), Sp, D(1), Sp, F.Id("else"), Sp, D(0))));
    }

    private static Formula TransformFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d");
        return All("n", Equal(Call("A174273", n), App(Qualified("Finset", "sum"),
            App(Qualified("Nat", "divisors"), n), Fun("d", Call("A035263", d)))));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n");
        return All("n", new Formula.Logic(
            Parenthesized(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, n)),
            FormulaLogicOperator.Implies,
            Parenthesized(Equal(Call("A378444", n), App(Qualified("Nat", "ceil"),
                new Formula.Fraction(Cast(Call("A174273", n), "Rat"), D(2)))))));
    }

    private static Formula All(string name, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), F.Id("Nat"), body);
    private static Formula Fun(string name, Formula body) => Parenthesized(Seq(
        F.Id("fun"), Sp, Parenthesized(Seq(F.Id(name), Colon, F.Id("Nat"))),
        Sp, Mapsto, Sp, body));
    private static Formula Cast(Formula value, string type) => Parenthesized(Seq(value, Colon, F.Id(type)));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
