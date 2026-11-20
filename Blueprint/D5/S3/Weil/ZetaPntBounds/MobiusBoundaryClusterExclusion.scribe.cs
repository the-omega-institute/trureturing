using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaPntBounds;

internal sealed class MobiusBoundaryClusterExclusionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaPntBounds/MobiusBoundaryClusterExclusion";
    private const string Boundary = "D5/S3/Weil/ZetaPntBounds/MobiusDyadicBoundary";
    private const string DyadicEnergy = "D5/S3/Weil/Mertens/MobiusDyadicEnergy";
    private const string KappaGap = "D5/S3/Arith/Robin/ForwardKernel/KappaGap";
    private const string HalfStripZero = "D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite critical Möbius energy excludes narrow selected clusters at the unattained zeta zero abscissa.",
        H("Zero clusters at the unattained zeta zero abscissa"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("high-selected-zero-cluster-exclusion"),
                DeclarationHandle.Create(
                    Owner + ".no_selectedZeroCluster_atHighOrdinate_of_unattainedZeroAbscissa"),
                H("Exclusion of narrow high zero clusters"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Sum, F.Underscore, F.Grp(F.Id("z")), F.Thin,
                    F.Id("D"), F.Open, F.Id("z"), F.Close, F.Neq, F.Sp, F.Id("q")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Θ < 1 be the unattained supremum of the real parts of nontrivial "
                        + "zeta zeros. For the finite sum S(x) of μ(n)/n over positive integers n ≤ x, "
                        + "assume that (S(x) − S(2x))² x^(1−2Θ) is integrable over x > 1. "
                        + "Fix real p > 0 and a positive integer q with p(2q − 1) > 2.")),
                    Paragraph(Text(
                        "There are positive R and T such that for every |t| ≥ T and every "
                        + "0 < r ≤ |t|^(−p), take any nonnegative divisor D dominated by the "
                        + "zeta divisor on the closed disk of radius R centered at Θ + it. "
                        + "If its support lies within the closed disk of radius r about the "
                        + "same center and strictly to the left of Θ, the sum of its selected "
                        + "multiplicities is different from q.")),
                    Paragraph(Text(
                        "A nontrivial zero with real part at least one half, together with "
                        + "unattainment, gives Θ > 1/2. The supremum property and zeta "
                        + "nonvanishing for real part at least one give a zero-free right "
                        + "half-plane away from the pole, and unattainment excludes line zeros. "
                        + "Three-circles interpolation and the logarithm estimates from "
                        + "ZetaReciprocalSubpolynomial give a fixed-disk bound of order |t|^ε. "
                        + "The analyticity and finite-order lemmas in StatementSeam justify "
                        + "factoring the selected divisor. This gives a lower bound on the "
                        + "weighted reciprocal-square mass on an interval of length 2r. "
                        + "The energy bound then forces 2 ≤ C |t|^(2+2ε) r^(2q−1) for a "
                        + "constant C, which fails at large |t| when "
                        + "2+2ε < p(2q−1)."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Boundary)),
            DocumentEdge.Dependency.Create(GidRef.Create(DyadicEnergy)),
            DocumentEdge.Dependency.Create(GidRef.Create(KappaGap)),
            DocumentEdge.Dependency.Create(GidRef.Create(HalfStripZero))
        ]));
}
