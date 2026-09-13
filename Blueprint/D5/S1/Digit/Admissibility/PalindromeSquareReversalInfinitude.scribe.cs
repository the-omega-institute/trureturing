using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Admissibility;

internal sealed class PalindromeSquareReversalInfinitudeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Digit/Admissibility/PalindromeSquareReversalInfinitude.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/brockhaus2007a133901");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Brockhaus and Seidov's sequence of palindromes with reversed-square witnesses is infinite.",
        H("Palindrome Squares and Their Reversals"),
        Blocks(
            Paragraph(Text(
                "All variables are natural numbers. Decimal digits are read by Nat.digits from "
                + "least significant to most significant; reversing that list before applying "
                + "ofDigits therefore reverses the ordinary decimal representation numerically.")),
            Node("rev10", "Decimal reversal", ReversalFormula(),
                "The value rev10(n) is the number whose decimal representation is obtained by "
                + "reversing the decimal representation of n. Nat.digits lists the least-significant "
                + "digit first.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsPalindrome10", "Decimal palindromes", PalindromeFormula(),
                "A natural number is a decimal palindrome exactly when decimal reversal leaves it "
                + "unchanged.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("IsMember", "Membership in A133901", MemberFormula(),
                "This is the intersection of A128921 with the requirement that the member's square "
                + "is not a palindrome: p is palindromic, p squared is not palindromic, and the "
                + "reversed square is itself a square.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("brockhaus_seidov_a133901", "Infinitude of A133901", InfinitudeFormula(),
                "For every natural bound B, the explicit decimal-block construction supplies a "
                + "larger palindrome p whose square is not a palindrome and whose reversed square "
                + "is a perfect square. Thus the sequence is unbounded and hence infinite.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a133901-palindrome-square-reversal-infinitude"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a133901-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula ReversalFormula()
    {
        Formula n = F.Id("n");
        return Disp(ForAll("n", Equal(
            Call("rev10", n),
            Call("ofDigits", D(1, 0), Call("reverse", Call("digits", D(1, 0), n))))));
    }

    private static Formula PalindromeFormula()
    {
        Formula n = F.Id("n");
        return Disp(ForAll("n", Iff(
            Call("IsPalindrome10", n),
            Parenthesized(Equal(Call("rev10", n), n)))));
    }

    private static Formula MemberFormula()
    {
        Formula p = F.Id("p");
        Formula square = Power(p, D(2));
        Formula q = F.Id("q");
        Formula squareWitness = Exists("q", Equal(Call("rev10", square), Power(q, D(2))));
        Formula conditions = And(
            Call("IsPalindrome10", p),
            And(new Formula.Not(Call("IsPalindrome10", square)), squareWitness));
        return Disp(ForAll("p", Iff(
            Call("IsMember", p), Parenthesized(conditions))));
    }

    private static Formula InfinitudeFormula()
    {
        Formula bound = F.Id("B");
        Formula p = F.Id("p");
        Formula witness = Exists("p", And(
            Less(bound, p), Call("IsMember", p)));
        return Disp(ForAll("B", witness));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula ForAll(string variable, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable), Naturals(), body);
    private static Formula Exists(string variable, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create(variable), Naturals(), body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);
}
