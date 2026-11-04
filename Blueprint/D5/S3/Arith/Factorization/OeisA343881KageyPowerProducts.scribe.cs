using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Factorization;

internal sealed class OeisA343881KageyPowerProductsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Factorization/OeisA343881KageyPowerProducts.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/kagey2021a343881");
    private const string TableQuote =
        "Table read by antidiagonals upward: T(n,k) is the least integer m > k such that "
        + "k^x * m^y = c^n for some positive integers c, x, and y where x < n and y < n; n >= 2, k >= 1.";
    private const string ConjectureQuote =
        "Conjecture: T(p,k) = A064549(k) for fixed k > 1 and sufficiently large p.";
    private const string RadicalQuote = "a(n) = n * Product_{primes p|n} p.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exponent coordinates of 12 and 72 refute eventual equality in A343881.",
        H("Kagey's Power-Product Conjecture Is False"), Blocks(
            Node("Works", "A power-product equation", WorksFormula(),
                TableQuote + " (OEIS A343881, NAME, revision 16; unpaginated.) "
                + "All variables are natural numbers. Positivity of c, x and y and the strict "
                + "bounds on both exponents are explicit.", AssessedProvenance.FromLiterature(Source)),
            Node("A064549", "The source's proposed value", RadicalFormula(),
                RadicalQuote + " (OEIS A064549, NAME, revision 71; unpaginated.) "
                + "The source index n is written k. Nat.primeFactors contains each prime divisor once.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The eventual-equality conjecture",
                Disp(Equivalent(F.Id("claim"), Parenthesized(ClaimBody()))),
                TableQuote + " (OEIS A343881, NAME, revision 16; unpaginated.) "
                + ConjectureQuote + " (OEIS A343881, COMMENT, revision 16; unpaginated.) "
                + "For every natural k greater than one there is a threshold N such that "
                + "the equality holds for every prime p at least N. Nat.find selects the least larger factor; the value is zero when no such factor exists.", AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("kagey-products-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Refutation at k = 12"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "At k=12 the proposed value is 72. If 12^x times 72^y were an nth power, "
                    + "its prime coordinates would give n dividing both 2x+3y and x+2y. "
                    + "Twice the latter minus the former is y, so n divides y, contradicting "
                    + "0<y<n. This obstruction holds for every natural n.")),
                    Paragraph(Text(
                    "For a prime p a larger factor exists: 27 works at p=2, while 144 works "
                    + "at p at least 3 with exponents p-2 and 1. Thus the least factor itself "
                    + "satisfies Works and cannot be 72. There are primes beyond every threshold, "
                    + "which disproves the eventual equality. The universal equality T(p,12)=144 "
                    + "for primes p at least 7 and a corrected formula for arbitrary k remain "
                    + "unproved here. The separate assertion that prime rows contain distinct "
                    + "integers also remains unresolved."))), DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kagey343881-powerproducts"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("kagey-products-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula WorksFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k"), m = F.Id("m");
        Formula c = F.Id("c"), x = F.Id("x"), y = F.Id("y");
        Formula equation = Equal(new Formula.Binary(new Formula.Power(k, x), FormulaBinaryOperator.Multiply, new Formula.Power(m, y)),
            new Formula.Power(c, n));
        Formula body = Some("c", Nat(), Some("x", Nat(), Some("y", Nat(),
            And(Less(D(0), c), And(Less(D(0), x), And(Less(D(0), y),
                And(Less(x, n), And(Less(y, n), equation))))))));
        return Disp(All("n", Nat(), All("k", Nat(), All("m", Nat(),
            Equivalent(Call("Works", n, k, m), Parenthesized(body))))));
    }

    private static Formula MinimumBody(Formula n, Formula k)
    {
        Formula m = F.Id("m");
        Formula exists = Some("m", Nat(), And(Less(k, m), Call("Works", n, k, m)));
        return Parenthesized(Seq(Keyword("if"), Sp, F.Id("h"), Sp, Colon, Sp,
            Parenthesized(exists), Sp, Keyword("then"), Sp, App(Q("Nat", "find"), F.Id("h")),
            Sp, Keyword("else"), Sp, D(0)));
    }

    private static Formula RadicalFormula()
    {
        Formula k = F.Id("k"), p = F.Id("p");
        Formula product = Seq(new Formula.Subscript(Prod,
            Seq(p, Sp, InMacro, Sp, App(Q("Nat", "primeFactors"), k))), Sp, p);
        return Disp(All("k", Nat(), Equal(Call("A064549", k), new Formula.Binary(k, FormulaBinaryOperator.Multiply, product))));
    }

    private static Formula ClaimBody()
    {
        Formula k = F.Id("k"), n = F.Id("N"), p = F.Id("p");
        return All("k", Nat(), Imply(Less(D(1), k), Some("N", Nat(), All("p", Nat(),
            Imply(App(Q("Nat", "Prime"), p), Imply(LeqF(n, p),
                Equal(MinimumBody(p, k), Call("A064549", k))))))));
    }

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Keyword(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Q(string owner, string name) => Seq(Keyword(owner), Dot, Keyword(name));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(F.Id(name), args);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeqF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Equivalent(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imply(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
