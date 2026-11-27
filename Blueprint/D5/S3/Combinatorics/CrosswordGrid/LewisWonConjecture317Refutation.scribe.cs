using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CrosswordGrid;

internal sealed class LewisWonConjecture317RefutationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/CrosswordGrid/LewisWonConjecture317Refutation";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/lewis2026crossword");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The only admissible balanced block size at n = 3 equals the strict lower endpoint.",
        H("The excluded endpoint in Lewis–Won Conjecture 3.17"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("claim"), DeclarationHandle.Create(Owner + ".claim"),
                H("The existential maximizer assertion"),
                StatementSource.FromAuthor(F.Disp(Conjecture())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Lewis and Won, §3.4, printed pp. 20–22. At p. 20, Eq. (3.1) "
                        + "defines E(n,m) below, with S(m,k) the Stirling number of the second "
                        + "kind. The complete summand is squared. Both m and the comparison "
                        + "size j are natural numbers with 1 ≤ m and 2m ≤ n, or the same "
                        + "bounds for j. The size bounds make the natural subtraction exact.")),
                    Paragraph(Math(F.Disp(Equation31()))),
                    Paragraph(Text("At p. 21 the lower cutoff x = m∗ is real, with x ≥ 1 "
                        + "and n ≥ 3. The equality uses the real cast of n. At p. 22 the "
                        + "conjecture asks for at least one global maximizer in the open interval "
                        + "(x, x + 2). Both endpoint comparisons use the real cast of m.")),
                    Paragraph(Math(F.Disp(Cutoff())))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"), DeclarationHandle.Create(Owner + ".result"),
                H("Refutation at size three"),
                StatementSource.FromAuthor(F.Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("At n = 3 and x = 1 the logarithms both equal "
                    + "log 2, which is positive. Their quotient is one and the cutoff equation "
                    + "reads 3 = 1 + 2. Every admissible positive size satisfies 1 ≤ m "
                    + "and 2m ≤ 3, hence m = 1. Its strict lower comparison would read "
                    + "1 < 1. The restriction to n ≥ 4 remains open."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("lewis-won-conjecture-3-17"), ResolutionKind.Refuted))),
        []));

    private static Formula Equation31()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var k = F.Id("k");
        var summation = F.Seq(F.Sum, F.Underscore, F.Grp(k, F.Eq, F.D(1)), F.Caret, F.Grp(m));
        var summand = F.Seq(F.Id("S"), F.Open, m, F.Comma, k, F.Close, F.Cdot, F.Sp,
            new Formula.Power(k, F.Seq(n, F.Minus, F.D(2), m)), F.Cdot, F.Sp, k, F.Bang);
        return F.Seq(F.Id("E"), F.Open, n, F.Comma, m, F.Close, F.Eq,
            summation, new Formula.Power(F.Seq(F.Open, summand, F.Close), F.D(2)));
    }

    private static Formula Cutoff()
    {
        var x = F.Id("x");
        var logarithms = new Formula.Fraction(
            F.Seq(F.Log, F.Open, x, F.Plus, F.D(1), F.Close),
            F.Seq(F.Log, F.Open, F.D(1), F.Plus, new Formula.Fraction(F.D(1), x), F.Close));
        return F.Seq(F.Id("n"), F.Eq, logarithms, F.Plus, F.D(2), x);
    }

    private static Formula Conjecture()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var j = F.Id("j");
        var x = F.Id("x");
        var naturals = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        var reals = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        var globalMaximum = F.Seq(F.Forall, F.Sp, j, F.InMacro, naturals, F.Comma,
            F.Open, F.D(1), F.Le, F.Sp, j, F.Land, F.Sp, F.D(2), j, F.Le, F.Sp, n, F.Close, F.Implies, F.Sp,
            F.Id("E"), F.Open, n, F.Comma, j, F.Close, F.Le, F.Sp,
            F.Id("E"), F.Open, n, F.Comma, m, F.Close);
        return new Formula.Aligned([
            F.Seq(F.Forall, F.Sp, n, F.InMacro, naturals, F.Comma, F.D(3), F.Le, F.Sp, n, F.Implies, F.Sp,
                F.Forall, F.Sp, x, F.InMacro, reals, F.Comma,
                F.Open, F.D(1), F.Le, F.Sp, x, F.Land, F.Sp, Cutoff(), F.Close, F.Implies),
            F.Seq(F.Exists, F.Sp, m, F.InMacro, naturals, F.Comma,
                F.Open, F.D(1), F.Le, F.Sp, m, F.Land, F.Sp, F.D(2), m, F.Le, F.Sp, n, F.Close, F.Land),
            F.Seq(F.Open, globalMaximum, F.Close, F.Land, F.Sp,
                x, F.Lt, m, F.Land, F.Sp, m, F.Lt, x, F.Plus, F.D(2)),
        ]);
    }
}
