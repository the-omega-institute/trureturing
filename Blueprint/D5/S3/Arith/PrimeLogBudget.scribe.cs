using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class PrimeLogBudgetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/PrimeLogBudget.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive real budget uniquely determines a threshold above two "
            + "through the sum of logarithmic prime ratios.",
        H("Prime Log Budget"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-log-budget"),
                DeclarationHandle.Create(Prefix + "primeLogBudget"),
                H("The prime log budget"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("y"), Sp, InMacro, Sp, RealDomain(), Comma, Sp,
                    Call("primeLogBudget", F.Id("y")), Sp, Eq, Sp,
                    Sum, Underscore,
                    Grp(Seq(F.Id("p"), Sp, InMacro, Sp,
                        Call("primesBelow", Call("natCeil", F.Id("y"))))), Sp,
                    Call("log", new Formula.Fraction(F.Id("y"), F.Id("p")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The index set is the natural primes strictly below the ceiling of y, "
                        + "so the summand is a finite sum of logarithmic ratios. A fixed "
                        + "upper cutoff retains the value as further primes enter the "
                        + "active set, which is what makes the total continuous in y."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unique-prime-threshold"),
                DeclarationHandle.Create(Prefix + "exists_unique_prime_log_budget"),
                H("A positive budget has exactly one threshold above two"),
                StatementSource.FromAuthor(ThresholdFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The statement quantifies over every positive real budget T. It "
                            + "asserts a unique real y with 2 < y whose prime log budget "
                            + "is exactly T. Uniqueness is part of the conclusion, not an "
                            + "added hypothesis.")),
                    Paragraph(Text(
                        "The proof shows the budget is continuous at every positive point "
                            + "and strictly monotone on the ray from two, evaluates it to "
                            + "zero at two, and bounds it below by a single logarithmic "
                            + "ratio. The intermediate value theorem then supplies existence "
                            + "on a closed interval and strict monotonicity supplies "
                            + "uniqueness.")),
                    Paragraph(Text(
                        "This module carries only the existence and uniqueness of the "
                            + "threshold. The optimal exponent formula, the closed form of "
                            + "the optimal value, and the budget constraint argument that "
                            + "uses them are not conclusions of this module."))),
                DescribeRole.Theorem))));

    private static Formula ThresholdFormula() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, F.Id("T"), Sp, InMacro, Sp, RealDomain(), Comma, Sp,
            D(0), Sp, Lt, Sp, F.Id("T"), Sp, Rightarrow),
        Seq(Exists, Bang, Sp, F.Id("y"), Sp, InMacro, Sp, RealDomain(), Comma, Sp,
            Open, D(2), Sp, Lt, Sp, F.Id("y"), Sp, Land, Sp,
            F.Id("T"), Sp, Eq, Sp, Call("primeLogBudget", F.Id("y")), Close, Dot)
    ]));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula RealDomain() => Seq(Mathbb, Grp(F.Id("R")));
}
