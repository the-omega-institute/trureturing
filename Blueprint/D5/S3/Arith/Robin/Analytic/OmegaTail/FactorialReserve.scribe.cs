using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaTail;

internal sealed class FactorialReserveDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal factorial threshold, its rounded reserves, and the retained prime base.",
        H("Prime reserves at a fixed factorial order"),
        Blocks(
            Definition("centered-threshold", "centeredThreshold", "Centered factorial threshold",
                "At a real prime cutoff P, multiply P by the sum of j!/(log P)^(j+1) over 0 ≤ j < r."),
            Definition("threshold", "threshold", "Factorial threshold",
                "Evaluate the centered threshold at log x."),
            Definition("tail-count", "tailCount", "Strict counting function",
                "Count integers from one through the natural floor of x whose number of distinct prime factors strictly exceeds the factorial threshold."),
            Definition("cutoff", "cutoff", "Integer cutoff",
                "Take the natural floor of the centered threshold and add one."),
            Definition("prime-excess", "primeExcess", "Real prime excess",
                "Subtract the integer cutoff from the number of primes at most P in real arithmetic."),
            Definition("deletion-count", "deletionCount", "Deletion count",
                "Use natural subtraction for the size of the deleted prime set."),
            Definition("continuous-reserve", "continuousReserve", "Continuous reserve",
                "Add P minus theta(P) to the unrounded prime excess times log P."),
            Definition("rounded-reserve", "roundedReserve", "Rounded reserve",
                "Add the real prime excess times log P to P minus theta(P)."),
            Definition("safe-reserve", "safeReserve", "Far deletion reserve",
                "Add the real prime excess times log(P/2) to P minus theta(P)."),
            Theorem("exact-cutoff", "tailCount_exp_eq", "Exact counting at exp P",
                "For P > 1 the strict inequality in the counting function is equivalent to meeting the integer cutoff, including when the threshold is an integer."),
            Theorem("continuous-reserve-limit", "continuous_reserve_limit", "Continuous reserve limit",
                "At each fixed order r the continuous reserve divided by P/(log P)^r tends to r!. "
                + "Multiplying the prime-counting residual by log P changes its scale from P/(log P)^(r+1) to P/(log P)^r. "
                + "The theta deficit divided by the latter scale tends to zero."),
            Theorem("reserve-limits", "factorial_reserve", "Factorial reserve limits",
                "At each fixed order r, the real prime excess divided by P/(log P)^(r+1) tends to r!. "
                + "The floor error is at most one and vanishes on this scale. Eventually the natural deletion count casts to the real excess. "
                + "The theta error is negligible on the scale P/(log P)^r and log(P/2)/log P tends to one. "
                + "Both reserves divided by P/(log P)^r therefore tend to r!."),
            Theorem("far-deletion", "factorial_far_deletion", "Exact far deletion",
                "Fix r ≥ 2. Eventually the desired deletion count is below the capacity of the prime window (P/2, 3P/4]. "
                + "Every subset of the prescribed size leaves exactly the integer cutoff of distinct primes. "
                + "All primes at most P outside the window are retained, and the logarithm of the retained product is at most P minus the far deletion reserve."))));

    private static DocumentBlock Definition(string id, string name, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string id, string name, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}
