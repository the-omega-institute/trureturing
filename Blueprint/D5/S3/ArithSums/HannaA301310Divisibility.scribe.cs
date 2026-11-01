using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class HannaA301310DivisibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/HannaA301310Divisibility.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/hanna2018geometricbinomial");
    private static Formula V(string name) => F.Id(name);
    private static Formula Naturals => Seq(Mathbb, Grp(V("N")));
    private static Formula Reals => Seq(Mathbb, Grp(V("R")));
    private static Formula Integers => new Formula.Integers();
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(Seq(V(owner), Dot, V(name))));
    private static Formula Choose(Formula upper, Formula lower) =>
        Seq(Qualified("Nat", "choose"), Parenthesized(upper), Sp, lower);
    private static Formula Pow(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula SomeInteger(Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("q"), Integers, body);
    private static Formula Implies(Formula premise, Formula body) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, body);
    private static Formula Positive(Formula n, Formula body) =>
        Implies(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, n), body);
    private static Formula Upper(Formula k, Formula n) =>
        Pow(k, D(2));
    private static Formula Term(Formula m, Formula k, Formula n, Formula denominator) =>
        new Formula.Fraction(Multiply(Pow(m, k), Typed(Choose(Upper(k, n), n), Reals)),
            Pow(denominator, Add(k, D(1))));
    private static Formula Series(Formula n) => Seq(
        Sum, Apos, Underscore, Grp(Seq(V("k"), Colon, Sp, Naturals)), Sp,
        Term(Typed(Num(2), Reals), V("k"), n, Typed(Num(3), Reals)));
    private static Formula ClaimBody() => All("n", Naturals, Positive(V("n"),
        SomeInteger(Equal(Call("a", V("n")), Multiply(Typed(Num(10), Reals),
            Typed(V("q"), Reals))))));
    private static Formula SumBody(bool rising)
    {
        var n = V("n");
        var m = V("m");
        var k = V("k");
        var upper = rising ? Subtract(Add(Pow(k, D(2)), n), D(1)) : Pow(k, D(2));
        var term = new Formula.Fraction(
            Multiply(Pow(Typed(m, Reals), k), Typed(Choose(upper, n), Reals)),
            Pow(Add(Typed(m, Reals), D(1)), Add(k, D(1))));
        var function = Parenthesized(Seq(V("fun"), Sp, Typed(k, Naturals), Sp,
            Mapsto, Sp, term));
        var value = Multiply(Multiply(Typed(m, Reals),
            Add(Multiply(D(2), Typed(m, Reals)), D(1))), Typed(V("q"), Reals));
        return All("n", Naturals,
            Implies(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, n),
                All("m", Naturals, SomeInteger(Call("HasSum", function, value)))));
    }
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hanna's A301310 coefficients are integer multiples of 10 at every positive index.",
        H("Hanna's A301310 divisibility conjecture"), Blocks(
            Node("a", "The source coefficient series",
                All("n", Naturals, Equal(Call("a", V("n")), Series(V("n")))),
                "OEIS A301310, FORMULA line 3 (unpaginated): a(n) = Sum_{k>=0} 2^k * binomial(k^2, n) / 3^(k+1). Here n and k range over natural numbers, Nat.choose is the ordinary natural binomial coefficient, and the infinite sum is taken in the real numbers.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The published positive-index assertion",
                Equal(V("claim"), ClaimBody()),
                "OEIS A301310, COMMENTS line 2 (unpaginated): a(n) is divisible by 10 for n>0 (conjecture). The positive integer index is encoded by 1 <= n, and divisibility is encoded by the existence of an integer q whose real multiple by 10 equals a(n).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("falling_hasSum", "Square-binomial geometric averages",
                SumBody(false),
                "For every positive n and natural m, the square-binomial series converges to m(2m+1) times an integer. Its finite integral numerator vanishes at zero and minus one, so it has the factor X(X+1). Homogenization preserves the integral quotient, including at m=0.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("rising_hasSum", "Rising square-binomial geometric averages",
                SumBody(true),
                "The same factorization applies to the even polynomial with natural values Nat.choose (k squared plus n minus one) n. Natural subtraction is used in the upper index. The series converges to m(2m+1) times an integer for every natural m.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("result", "The divisibility theorem", ClaimBody(),
                "The convergent geometric average at m=2 is m(2m+1) times an integer, giving the factor 10. Summability is proved before identifying the infinite sum.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("hanna301310-" + name.Replace("_", "").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);
}
