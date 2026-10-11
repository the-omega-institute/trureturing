using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class SequentialHellingerLocalizationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Observer/liptser2001sequential");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite predictable energy gives simultaneous convergence on one full-measure set.",
        H("Common Predictable-Energy Localization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("common-energy-localization"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SequentialHellingerLocalization.common_energy_localization"),
                H("Joint moment control and finite-energy convergence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let mu be a probability measure and F a filtration indexed by the natural numbers. "
                        + "The integrable energy e(n) is F(n)-measurable and takes values in [0,1]. "
                        + "The centered increment d(n) and nonnegative error y(n) are measurable at n+1. "
                        + "Each d(n) is square integrable, each y(n) is integrable, and the conditional "
                        + "mean of d(n) is zero. Their conditional second and first moments, respectively, "
                        + "are at most twice e(n). No uniform bound on d(n) or y(n) is required.")),
                    Paragraph(Text(
                        "For every nonnegative integer K, retain increment n exactly when the sum of "
                        + "e(i) over i less than n is at most K. At every horizon, the second moment of "
                        + "the retained centered sum and the mean of the retained error sum are both at "
                        + "most 2(K+1). The extra one allows the final retained increment to cross K.")),
                    Paragraph(Text(
                        "There is one full-measure set on which every path with summable energy has "
                        + "convergent natural-order centered partial sums and a summable nonnegative "
                        + "error sequence. The centered series is not asserted to converge absolutely. "
                        + "The argument first applies martingale convergence to each retained process, "
                        + "then intersects the countably many full-measure sets. A path with finite "
                        + "energy admits an integer level at which every original increment is retained."))),
                DescribeRole.Theorem))));
}
