using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class CentralStirlingOddSquareDivisibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/CentralStirlingOddSquareDivisibility.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/bala2025a007820");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every odd column of the central Stirling numbers is divisible by the square of that column.",
        H("Square Divisibility of Odd Central Stirling Numbers"),
        Blocks(
            Node("claim", "Bala's assertion",
                Disp(Seq(Operatorname, Grp(F.Id("claim")), Sp, Iff, Sp, ClaimBody())),
                "OEIS A007820, COMMENTS (unnumbered web entry), states verbatim: "
                    + "\"%C Conjecture: a(2*n+1) is divisible by (2*n + 1)^2. - _Peter Bala_, Mar 30 2025\" "
                    + "Its NAME is \"%N Stirling numbers of second kind S(2n,n).\" "
                    + "Here n ranges over all natural numbers, including zero. "
                    + "Nat.stirlingSecond r k counts partitions of an r-element labelled set "
                    + "into exactly k nonempty, unlabelled blocks. The column is 2*n+1 and "
                    + "the row is twice that column; divisibility is in the natural numbers.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The assertion holds", Disp(ClaimBody()),
                "Integer inclusion-exclusion expresses the factorial-weighted Stirling number "
                    + "as an alternating binomial sum. Reflecting its index and expanding by "
                    + "the binomial theorem gives a reflection identity for every natural column m, "
                    + "including zero. For odd m its zero-order term is the negative of the "
                    + "central Stirling number. The first-order term contains 2*m^2, and "
                    + "each higher-order term contains m^2. Thus m^2 divides twice the central "
                    + "Stirling number. Since m^2 is coprime to two, it divides the number itself. "
                    + "Setting m=2*n+1 proves the assertion, including n=0 and all odd composite columns.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bala-a007820"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("bala-a007820-" + name), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), provenance,
        Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        var column = Parenthesized(new Formula.Binary(
            new Formula.Binary(D(2), FormulaBinaryOperator.Multiply, n),
            FormulaBinaryOperator.Add, D(1)));
        var row = new Formula.Binary(D(2), FormulaBinaryOperator.Multiply, column);
        return Seq(Forall, Sp, n, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            new Formula.Power(column, D(2)), Sp, Mid, Sp,
            new Formula.Apply(Qualified("Nat", "stirlingSecond"), [row, column]));
    }

    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));

    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
}
