using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class TwoDenseDivisorBlocksPalindromeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/TwoDenseDivisorBlocksPalindrome.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/pol2025a384222");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The maximal two-dense divisor blocks form a palindromic composition.",
        H("Two-Dense Divisor Blocks Are Palindromic"),
        Blocks(
            Paragraph(Text("Omar E. Pol's June 3, 2025 entry OEIS A384222 states "
                + "Conjecture 1: row n is a palindromic composition of A000005(n). "
                + "The proof here applies to every positive natural n.")),
            Paragraph(Text("The function splitBy retains adjacent entries a,b in the "
                + "same maximal block exactly when its Boolean relation is true. "
                + "The first coordinates of divisorsAntidiagonalList(n) list every "
                + "positive divisor once, in increasing order. All lengths and indices "
                + "are natural numbers.")),
            Node("twoDenseBlockLengths", "Lengths of the maximal blocks", BlocksFormula(),
                "Cut precisely where b exceeds twice a, and take the length of each "
                + "resulting nonempty block.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("row", "The row of OEIS A384222", RowFormula(),
                "Apply the block-length function to the increasing divisor list. "
                + "Mathlib uses an empty divisor list at n=0.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("row_sum", "The sum is the divisor count", SumFormula(),
                "Flattening splitBy restores the original list. Its distinct entries "
                + "are exactly the positive divisors, so the sum of the block lengths "
                + "equals the cardinality of divisors(n).",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("row_palindrome", "Conjecture 1", PalindromeFormula(),
                "The divisor complement d maps to n divided by d, using natural integer "
                + "division, and reverses the divisor list. For divisors a,b, the relation "
                + "b at most twice a is equivalent to the complement of a being at most "
                + "twice the complement of b. A general reversal lemma constructs the "
                + "reversed block decomposition and verifies both its internal links "
                + "and its separating boundaries using splitBy uniqueness. Taking "
                + "lengths gives the palindrome. The sum theorem and nonemptiness of "
                + "every block complete the composition assertion.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a384222-two-dense-divisor-blocks-palindrome"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("two-dense-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula N() => F.Id("n");
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args)
    {
        var pieces = new List<Formula>();
        foreach (var arg in args)
        {
            if (pieces.Count > 0) pieces.AddRange([Comma, Sp]);
            pieces.Add(arg);
        }
        return Seq(Named(name), Parenthesized(Seq(pieces.ToArray())));
    }
    private static Formula Universal(Formula body) => Disp(Seq(
        Forall, Sp, N(), Colon, Sp, Nat(), Comma, Sp, body));
    private static Formula Positive(Formula body) => Universal(Seq(
        D(0), Sp, Lt, Sp, N(), Sp, Implies, Sp, body));
    private static Formula Row() => Call("row", N());

    private static Formula BlocksFormula() => Disp(Seq(
        Forall, Sp, F.Id("l"), Colon, Sp, Call("List", Nat()), Comma, Sp,
        Call("twoDenseBlockLengths", F.Id("l")), Sp, Eq, Sp,
        Call("map", Named("length"), Call("splitBy",
            Parenthesized(Seq(F.Id("a"), Sp, F.Id("b"), Sp, Mapsto, Sp,
                Call("decide", Seq(F.Id("b"), Sp, Le, Sp, D(2), Cdot, Sp, F.Id("a"))))),
            F.Id("l")))));

    private static Formula RowFormula() => Universal(Seq(Row(), Sp, Eq, Sp,
        Call("twoDenseBlockLengths", Call("map", Named("fst"),
            Call("divisorsAntidiagonalList", N())))));

    private static Formula SumFormula() => Positive(Seq(
        Call("sum", Row()), Sp, Eq, Sp, Call("card", Call("divisors", N()))));

    private static Formula PalindromeFormula() => Positive(Seq(
        Call("reverse", Row()), Sp, Eq, Sp, Row()));

}
