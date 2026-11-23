using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Parking;

internal sealed class DescentGapKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Parking/DescentGapKernel.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/alexandersson2026parking");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two ordered boundary gaps, three single comparisons and the paired comparisons at each old strict peak determine the insertion weight.",
        H("Gap weights for peaks, ties and descents"),
        Blocks(
            Node("Edge", "Adjacent comparisons", DescribeRole.Definition,
                "An adjacent pair is a strict ascent, a tie or a strict descent."),
            Node("edges", "Read the comparisons", DescribeRole.Definition,
                "Read one comparison for every consecutive pair in the literal word."),
            Node("peaks", "Strict interior peaks", DescribeRole.Definition,
                "For each consecutive triple a, b, c, count the middle letter once when both a < b and c < b."),
            Node("ties", "Adjacent ties", DescribeRole.Definition,
                "Count equal consecutive pairs using the word and its one-letter tail."),
            Node("wordWeight", "The literal trivariate weight", DescribeRole.Definition,
                "A word of p strict interior peaks, k adjacent ties and d strict adjacent descents has weight t^p u^k v^d."),
            Node("wordWeight_replicate", "Weight of the constant one word", DescribeRole.Theorem,
                "The word of n ones has no peaks or descents and exactly n − 1 adjacent ties."),
            Node("consEmbedding", "Prepend a gap size", DescribeRole.Definition,
                "An injective map prepends a fixed natural number to a list."),
            Node("profiles", "Profiles of fixed arity and mass", DescribeRole.Definition,
                "Enumerate all lists of k gap sizes totaling r by splitting r between the first size and the remaining list."),
            Node("mem_profiles", "Meaning of profile membership", DescribeRole.Theorem,
                "A list lies in the finite profile set exactly when its length equals k and its sum equals r."),
            Node("boundarySeries", "Positive boundary run", DescribeRole.Definition,
                "A boundary run of j ≥ 1 new maxima contributes u^(j−1) at degree j."),
            Node("occupiedSeries", "Occupied internal gap", DescribeRole.Definition,
                "A single inserted maximum contributes t at degree one. A run of j ≥ 2 new maxima contributes u^(j−1) at degree j."),
            Node("leftSeries", "Left boundary factor", DescribeRole.Definition,
                "The empty left gap contributes one. A nonempty run has an additional descent into the first old letter."),
            Node("rightSeries", "Right boundary factor", DescribeRole.Definition,
                "The empty right gap contributes one. A nonempty run contributes its ties and has an ascent from the last old letter."),
            Node("singleSeries", "Unpaired interior comparison", DescribeRole.Definition,
                "An empty gap keeps its original ascent, descent or tie weight. A nonempty gap contributes the occupied internal gap weight and a descent."),
            Node("peakSeries", "The paired gaps at an old peak", DescribeRole.Definition,
                "If neither gap is occupied, the old peak and descent contribute tv. With just one gap occupied, the two orientations contribute vS and v²S for the occupied series S. If both are occupied they contribute v²S²."),
            Node("insertionSeries", "Series from ordered comparison blocks", DescribeRole.Definition,
                "Scan the comparisons and pair each ascent immediately followed by a descent. Multiply their two-gap factors, the remaining comparison factors and the two boundary factors."),
            Node("closedKernel", "Six-factor kernel", DescribeRole.Definition,
                "For a nonempty word of length ℓ, use one factor per boundary, ℓ − 1 − d − k − p unpaired ascents, d − p unpaired descents, k ties and p old peak blocks."),
            Node("insertionSeries_closed", "Counting the six types", DescribeRole.Theorem,
                "Each paired block consumes one ascent and one descent. Block counts therefore reduce the ordered product to the six-factor kernel."),
            Node("closedKernel_coeff", "Local coefficient formula", DescribeRole.Theorem,
                "For a nonempty word whose letters are below m, the coefficient of z^r in the six-factor kernel equals the sum of the literal word weights obtained by inserting r copies of m into its ordered gaps."),
            Node("geometricDenominator", "The geometric unit", DescribeRole.Definition,
                "The series 1 − uz is a unit. Rescaling the geometric identity by u gives the inverse with coefficient u^j at degree j."),
            Node("bivarE", "Bivariate boundary factor", DescribeRole.Definition,
                "E is one plus the positive boundary series."),
            Node("bivarA", "Bivariate comparison factor", DescribeRole.Definition,
                "A is one plus the occupied internal gap series."),
            Node("bivarC", "Bivariate tie factor", DescribeRole.Definition,
                "C is u plus the occupied internal gap series."),
            Node("bivarB", "Bivariate old-peak factor", DescribeRole.Definition,
                "B is A² + t − 1."),
            Node("bivariateFactors_eq10", "The four series of equation (10)", DescribeRole.Theorem,
                "E is 1 + z/(1 − uz), A is 1 + tz + uz²/(1 − uz), C is u + tz + uz²/(1 − uz), and B is A² + t − 1. The geometric denominator is the specified power-series unit."),
            Node("ascentUnit", "The comparison factor as a unit", DescribeRole.Definition,
                "A has constant coefficient one and uses the formal inverse determined by that unit coefficient."),
            Node("insertionSeries_eq11", "Equation (11) on each word weight", DescribeRole.Theorem,
                "At v = 1 the boundary factors coincide and the ascent and descent factors both become A. Cancelling the inverse powers of A gives E² A^(ℓ−1) (B/A²)^p (C/A)^k.")),
        []));

    private static DocumentBlock Node(
        string declaration, string title, DescribeRole role, string prose,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("descentgapkernel-" + declaration.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))),
            role, resolution);
}
