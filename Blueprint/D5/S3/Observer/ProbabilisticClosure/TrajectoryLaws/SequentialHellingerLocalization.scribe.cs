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
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-energy-positive-product"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SequentialHellingerLocalization.finite_energy_positive_product"),
                H("Strictly positive product limits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let r(n) be strictly positive, square integrable and measurable at time n+1. "
                        + "Suppose its conditional mean is 1-e(n), and the conditional mean of "
                        + "(r(n)-1) squared is at most 2e(n), with predictable e(n) in [0,1]. "
                        + "Almost every path with summable energy has a strictly positive finite "
                        + "limit of the products of r(i) for i less than n.")),
                    Paragraph(Text(
                        "Conditional variance bounds the squared centered increment by the same "
                        + "conditional error moment. Common energy localization therefore gives "
                        + "convergence of the centered sums and summability of (r(n)-1) squared. "
                        + "Subtracting the finite energy drift gives convergence of the sums of "
                        + "r(n)-1. The logarithmic remainder is eventually bounded by twice its "
                        + "square. Hence the natural-order logarithmic sums converge to a finite "
                        + "real number, whose exponential is the positive product limit. No "
                        + "uniform positive lower bound on the individual r(n) is imposed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("trajectory-finite-energy-positive-likelihood"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SequentialHellingerLocalization.trajectory_finite_energy_positive_likelihood"),
                H("Actual full-history likelihoods"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For a nonempty finite discrete alphabet, let p and q be strictly positive "
                        + "normalized rows indexed by finite histories. Let H(n,x) be the first n "
                        + "letters of x and let rho(h) be the sum over letters of the square root "
                        + "of p(h,a)q(h,a). Under trajectoryLaw(p), almost every path with summable "
                        + "1-rho(H(n,x)) has a positive finite limit of the products of "
                        + "q(H(i,x),x(i))/p(H(i,x),x(i)) over i less than n.")),
                    Paragraph(Text(
                        "The conditional distribution of the next letter is the row at the actual "
                        + "observed history. This identifies the two conditional root-likelihood "
                        + "moments used above. Each fixed-time increment has finite range, so it is "
                        + "square integrable even though no uniform bound across time is assumed. "
                        + "The initial-letter factor is included explicitly after applying the "
                        + "conditional argument to successor coordinates. Squaring the positive "
                        + "root-product limit gives the stated likelihood limit."))),
                DescribeRole.Theorem))));
}
