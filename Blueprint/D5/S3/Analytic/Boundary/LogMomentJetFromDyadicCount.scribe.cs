using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Boundary;

internal sealed class LogMomentJetFromDyadicCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A logarithmic dyadic counting gain yields finite lower-order boundary log moments.",
        H("Boundary Logarithmic Jets from Dyadic Counts"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("summable-log-moment-from-dyadic-count"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Boundary/LogMomentJetFromDyadicCount."
                    + "summable_log_moment_of_dyadic_count"),
                H("A k-fold counting gain gives every log moment below k minus one"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let A contain only natural numbers at least two. Its j-th shell S_j is "
                        + "the exact fiber on which the natural base-two logarithm equals j. If "
                        + "the shell cardinality is at most C 2^j/(j+1)^k, then every logarithmic "
                        + "boundary moment of integral order m with m+1<k is summable.")),
                    Paragraph(Text(
                        "Inside shell j, 2^j <= n < 2^(j+1). Monotonicity and the power law for "
                        + "the real logarithm bound (log n)^m/n by (((j+1)log 2)^m)/2^j. "
                        + "Multiplying by the shell count cancels the exponential factor and m "
                        + "powers of j+1. Since k is at least m+2, the shell sum is bounded by a "
                        + "constant multiple of 1/(j+1)^2, a shifted p-series.")),
                    Paragraph(Text(
                        "Mathlib's summable_partition then reassembles the exact shell fibers, and "
                        + "summable_subtype_iff_indicator returns the original series over A rather "
                        + "than merely a series of shell bounds. Exact shell coverage is an explicit "
                        + "hypothesis, so no elements of A can be omitted from the counting data.")),
                    Paragraph(Text(
                        "The source uses a Vinogradov bound with a real exponent beta. The formal "
                        + "statement specializes it to the integer pattern exponent k used by the "
                        + "source's jet table and makes the hidden constant C explicit. Passing from "
                        + "the cumulative estimate N_A(x) << x/(log x)^k to the displayed dyadic "
                        + "estimate only changes C by fixed powers of 2 and log 2. The condition "
                        + "m<k-1 is written m+1<k to avoid truncated natural subtraction. The "
                        + "restriction n>=2 excludes Lean's totalized log-zero and division-by-zero "
                        + "branches; finitely many smaller indices do not affect convergence. No "
                        + "critical-order divergence or numerical pattern-count certificate is claimed.")),
                    Paragraph(Text(
                        "Six duplicate routes were checked: Lean keywords; mathematical notation "
                        + "and naming variants; current accepted-event receipts; digestion backfill "
                        + "and digest text by source hash; generalized Abel-summation, partition, "
                        + "p-series, and smooth-series searches; and all in-flight math lanes. No "
                        + "equivalent D5 or pinned-Mathlib theorem was found. The exact upstream "
                        + "lemmas reused are summable_partition, summable_subtype_iff_indicator, "
                        + "Real.summable_nat_pow_inv, Nat.pow_log_le_self, "
                        + "Nat.lt_pow_succ_log_self, Real.log_le_log, and Real.log_pow. The legacy "
                        + "formalization-receipt directory is retired on the current branch."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("n");
        Formula j = F.Id("j");
        Formula m = F.Id("m");
        Formula k = F.Id("k");
        Formula c = F.Id("C");
        Formula set = F.Id("A");
        Formula shell = Seq(F.Id("S"), Underscore, Grp(j));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula natLog = Seq(
            Operatorname, Grp(F.Id("NatLog")), Underscore, Grp(D(2)), Open, n, Close);
        Formula positiveNaturals = Seq(
            OpenBrace, n, Sp, InMacro, Sp, naturals, Sp, Mid, Sp,
            D(2), Le, Sp, n, CloseBrace);
        Formula shellSet = Seq(
            OpenBrace, n, Sp, InMacro, Sp, set, Sp, Mid, Sp,
            natLog, Eq, j, CloseBrace);
        Formula shellBound = Seq(
            Lvert, Sp, shell, Rvert, Le,
            Frac,
            Grp(c, Sp, D(2), Caret, Grp(j)),
            Grp(Open, j, Plus, D(1), Close, Caret, Grp(k)));
        Formula logMoment = Seq(
            Frac,
            Grp(Open, Log, Open, n, Close, Close, Caret, Grp(m)),
            Grp(n));

        return Disp(new Formula.Aligned([
            Seq(
                set, Sp, Subseteq, Sp, positiveNaturals, Comma, Sp,
                m, Comma, k, Sp, InMacro, Sp, naturals, Comma, Sp,
                c, Sp, InMacro, Sp, reals, Comma),
            Seq(
                D(0), Le, Sp, c, Comma, Sp, m, Plus, D(1), Lt, Sp, k, Comma),
            Seq(
                Forall, Sp, j, Sp, InMacro, Sp, naturals, Comma, Sp,
                shell, Eq, shellSet, Comma, Sp, shellBound, Sp, Rightarrow),
            Seq(
                Sum, Underscore, Grp(n, Sp, InMacro, Sp, set),
                logMoment, Sp, Lt, Sp, Infty, Dot),
        ]));
    }
}
