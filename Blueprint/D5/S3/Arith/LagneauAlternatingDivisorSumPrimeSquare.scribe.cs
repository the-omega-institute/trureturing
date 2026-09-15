using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class LagneauAlternatingDivisorSumPrimeSquareDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/LagneauAlternatingDivisorSumPrimeSquare.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/lagneau2012a193351");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A prime alternating sum of decreasing divisors above three forces a square or twice a square.",
        H("Lagneau's Alternating Divisor-Sum Conjecture"),
        Blocks(
            Node("T", "The alternating divisor sum", DefinitionFormula(),
                "For each natural number n, T(n) is the integer alternating sum of its "
                + "divisors nonincreasing, starting with n. Each divisor is coerced to an "
                + "integer before the alternating sum is taken.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("lagneau_a193351", "Lagneau's A193351 conjecture", TheoremFormula(),
                "Pairing the decreasing divisors gives T(n) at least n/2. For n greater "
                + "than three, a prime T(n) is therefore not two and hence is odd. "
                + "Alternating signs disappear modulo two, so T(n) has the parity of "
                + "sigma(n). The classical characterization of odd sigma values then "
                + "gives that n is a square or twice a square.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a193351-alternating-divisor-sum-prime-square"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a193351-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula DefinitionFormula()
    {
        var n = F.Id("n");
        var d = F.Id("d");
        var comparator = Parenthesized(Seq(
            new Formula.Placeholder(), Sp, Ge, Sp, new Formula.Placeholder()));
        var coercion = Parenthesized(Seq(
            LambdaLower, Sp, d, Sp, InMacro, Sp, Naturals(), Sp, Mapsto, Sp,
            Parenthesized(Seq(d, Sp, Colon, Sp, new Formula.Integers()))));
        var sortedDivisors = Call("sort", Call("divisors", n), comparator);
        var mappedDivisors = Call("map", sortedDivisors, coercion);
        return Disp(Equal(Call("T", n), Call("alternatingSum", mappedDivisors)));
    }

    private static Formula TheoremFormula()
    {
        var n = F.Id("n");
        var t = F.Id("t");
        var square = ExistsNatural("t", Equal(n, Square(t)));
        var twiceSquare = ExistsNatural("t", Equal(n, Multiply(D(2), Square(t))));
        var conclusion = Or(square, twiceSquare);
        var body = Implies(Less(D(3), n),
            Implies(Call("Prime", Call("toNat", Call("T", n))), conclusion));
        return Disp(ForAllNatural("n", body));
    }

    private static Formula Naturals() =>
        Seq(Mathbb, new Formula.LatexGroup([F.Id("N")]));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula ForAllNatural(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Naturals(), body);
    private static Formula ExistsNatural(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Naturals(), body);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies,
            Parenthesized(right));
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or,
            Parenthesized(right));
    private static Formula Square(Formula value) => new Formula.Power(value, D(2));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
