using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaTail;

internal sealed class FarDeletionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Centered prime excess and the logarithmic reserve retained after far deletion.",
        H("Far deletion at the second distinct-prime threshold"),
        Blocks(
            Definition("centered-threshold", "centeredThreshold", "Continuous threshold",
                "At a real cutoff P, put l = log(P) and a(P) = P/l + P/l^2."),
            Definition("centered-count", "centeredCount", "Strict rounded count",
                "Use the second-order selection count with parameter one at exp(P). For P > 1 this is k(P) = floor(a(P)) + 1, including integer values of a(P)."),
            Definition("prime-excess", "primeExcess", "Real prime excess",
                "The difference e(P) = pi(P) - k(P) uses the number of primes at most P."),
            Definition("deletion-count", "deletionCount", "Natural deletion count",
                "The deletion cardinality is the natural subtraction pi(P) - k(P). Eventually its real cast equals e(P)."),
            Definition("continuous-reserve", "continuousReserve", "Continuous reserve",
                "The continuous reserve B0(P) is P - theta(P) + (pi(P) - a(P))*l."),
            Definition("rounded-reserve", "roundedReserve", "Rounded reserve",
                "The rounded reserve Bk(P) is P - theta(P) + e(P)*l."),
            Definition("safe-reserve", "safeReserve", "Far deletion reserve",
                "The reserve Dsafe(P) is P - theta(P) + e(P)*log(P/2)."),
            Describe.Lean(DescribeId.Create("centered-reserve"),
                DeclarationHandle.Create(Prefix + "centered_reserve"), H("Centered prime and reserve limits"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("As the real cutoff P tends to infinity, e(P)/(P/l^3) tends to 2. "
                        + "On P > 1 the rounding error k(P) - a(P) is strictly positive and at most one. "
                        + "Eventually e(P) is nonnegative and is the real cast of the deletion count. "
                        + "Each of B0(P), Bk(P) and Dsafe(P), divided by P/l^2, tends to 2.")),
                    Paragraph(Text("Subtract the first two terms of the frozen prime-counting expansion "
                        + "and divide by P/l^3. The fourth term and the normalized remainder tend to zero. "
                        + "The floor error is bounded on the same scale. The theta error divided by P/l^2 "
                        + "tends to zero, and log(P/2)/l tends to one."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("far-window-capacity"),
                DeclarationHandle.Create(Prefix + "far_window_capacity"), H("Far window capacity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The number of primes in (P/2, 3P/4] divided by P/log(P) tends to 1/4."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("far-deletion-of-card-le"),
                DeclarationHandle.Create(Prefix + "far_deletion_of_card_le"), H("Uniform budget for feasible deletions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the window can accommodate the difference between the prime count and a prescribed cardinality, "
                    + "choose a subset of precisely that size. Every such subset leaves the prescribed cardinality. "
                    + "Each deleted prime pays at least log(P/2) toward the logarithmic reserve."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("far-deletion"),
                DeclarationHandle.Create(Prefix + "far_deletion"), H("Existence and uniform log budget"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every sufficiently large real P, the window J(P) consists of the "
                        + "primes in (P/2, 3P/4]. It admits a subset R of size e(P). For every such R, "
                        + "the primes at most P outside R number exactly k(P), and the sum of their logarithms "
                        + "is at most P - Dsafe(P).")),
                    Paragraph(Text("On the common scale P/l the window capacity tends to 1/4 and the "
                        + "deletion count tends to zero. Every deleted prime contributes at least log(P/2), "
                        + "so subtracting the removed sum from theta(P) gives the uniform budget. "
                        + "The argument allows either sign of P - theta(P)."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string id, string name, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), DescribeRole.Definition);
}
