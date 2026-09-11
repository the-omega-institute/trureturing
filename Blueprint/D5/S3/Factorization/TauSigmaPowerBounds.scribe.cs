using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class TauSigmaPowerBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/TauSigmaPowerBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform fourth-power estimates for the divisor count and divisor sum.",
        H("Divisor Count and Sum Bounds"),
        Blocks(
            Paragraph(Text("These estimates hold for every natural number, including zero. "
                + "They supply the analytic premises for the bound on positive solutions of "
                + "Ivan N. Ianakiev's equality conjecture in OEIS A336687.")),
            Describe.Lean(
                DescribeId.Create("tau-fourth-power"),
                DeclarationHandle.Create(Prefix + "tau_pow_four_le"),
                H("Uniform divisor-count bound"),
                StatementSource.FromAuthor(BoundFormula(false)),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Arith/ianakiev2020a336687")),
                Blocks(Paragraph(Text("On prime powers, the consecutive quotient decreases "
                    + "after a finite initial segment. The six exceptional prime costs have "
                    + "product 127401984/25025, less than 9^4. Multiplying over the distinct "
                    + "prime factors proves tau(n)^4 <= 9^4*n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sigma-fourth-power"),
                DeclarationHandle.Create(Prefix + "sigma_pow_four_le"),
                H("Uniform divisor-sum bound"),
                StatementSource.FromAuthor(BoundFormula(true)),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Arith/ianakiev2020a336687")),
                Blocks(Paragraph(Text("The prime-power geometric sums have exceptional "
                    + "costs 81/32 at two and 256/243 at three. All primes at least five "
                    + "have cost one. Their product is 8/3, less than three. This proves "
                    + "sigma(n)^4 <= 3*n^5 by multiplicativity."))),
                DescribeRole.Theorem))));

    private static Formula BoundFormula(bool sum)
    {
        var n = F.Id("n");
        Formula left = new Formula.Power(
            Seq(Operatorname, Grp(F.Id(sum ? "sigma" : "tau")), Open, n, Close), D(4));
        Formula right = sum
            ? new Formula.Binary(D(3), FormulaBinaryOperator.Multiply, new Formula.Power(n, D(5)))
            : new Formula.Binary(new Formula.Power(D(9), D(4)), FormulaBinaryOperator.Multiply, n);
        return Disp(Seq(Forall, Sp, n, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right)));
    }
}
