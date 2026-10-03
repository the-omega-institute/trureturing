using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class TauCubeRootBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A sharp cubic-root estimate for the number of positive divisors.",
        H("Sharp Divisor-Count Bound"),
        Blocks(
            Paragraph(Text("Write tau(j) for the cardinality of the positive divisors of j.")),
            Describe.Lean(
                DescribeId.Create("sharp-divisor-count-cubic-root-bound"),
                DeclarationHandle.Create("D5/S3/Factorization/TauCubeRootBound.result"),
                H("Cubic-root bound and equality case"),
                StatementSource.FromAuthor(Claim()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive j, factorization expresses tau(j) as the product "
                    + "of one plus each prime exponent. Cubing these factors gives sharp "
                    + "local costs 8, 3, 8/5, and 8/7 at primes 2, 3, 5, and 7, "
                    + "respectively; every larger prime has cost one. A decreasing "
                    + "consecutive quotient extends the finite base checks to all "
                    + "exponents. Their product is 1536/35, so 35 tau(j)^3 <= 1536 j. "
                    + "Taking nonnegative cube roots yields the first bound. Since "
                    + "3/35 < 1/8, its coefficient is strictly below four. At "
                    + "j = 2520 = 2^3 3^2 5 7, the divisor count is 48 and every "
                    + "local estimate is an equality."))),
                DescribeRole.Theorem))));

    private static Formula Claim()
    {
        var j = F.Id("j");
        var root = Pow(Frac(D(3), Num(35)), Frac(D(1), D(3)));
        var jRoot = Pow(j, Frac(D(1), D(3)));
        var upper = Mul(Mul(D(8), root), jRoot);
        return Disp(Seq(Open,
            Forall, Sp, j, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            D(0), Sp, Lt, Sp, j, Sp, Rightarrow, Sp,
            Tau(j), Sp, Le, Sp, upper, Sp, Lt, Sp, Mul(D(4), jRoot),
            Close, Sp, Land, Sp, Tau(Num(2520)), Sp, Eq, Sp,
            Mul(Mul(D(8), root), Pow(Num(2520), Frac(D(1), D(3))))));
    }

    private static Formula Tau(Formula x) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id("tau"))), [x]);
    private static Formula Pow(Formula x, Formula y) => Seq(Grp(x), Caret, Grp(y));
    private static Formula Frac(Formula x, Formula y) => Seq(F.Frac, Grp(x), Grp(y));
    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
}
