using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class PrimeTrianglePowerWindowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordinary-prime triangle characterizes RH on arbitrarily late power windows.",
        H("Ordinary-prime triangles on power windows"),
        Blocks(Describe.Lean(
            DescribeId.Create("rh-iff-frequently-prime-triangle-lower"),
            DeclarationHandle.Create(
                "D5/S3/Weil/Mertens/IntegratedExplicit/PrimeTrianglePowerWindow.rh_iff_frequently_prime_triangle_lower"),
            H("One lower bound on arbitrarily late windows"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Fix any real b > 1. The Riemann hypothesis is equivalent to the existence "
                    + "of one C ≥ 0 such that, for arbitrarily large X, the ordinary-prime "
                    + "triangle sum is at least 2x log 2 − C√x at every real x in [X, Xᵇ].")),
                Paragraph(Text(
                    "For the converse, the filtered Laplace transform retains a nonzero "
                    + "residue at a zero off the critical line. A complex disk isolating a "
                    + "pole and a zero-free disk at its real projection separate the high "
                    + "Taylor coefficients. Gamma weights concentrate the corresponding "
                    + "signed moments in the logarithmic image of the power window. "
                    + "The prime-power error is bounded by a fixed multiple of √x. "
                    + "An off-line zero therefore forces a violation of the lower bound "
                    + "in every sufficiently late window.")),
                Paragraph(Text(
                    "The use of localized oscillation has the classical precedent of "
                    + "Kaczorowski and Pintz, Oscillatory properties of arithmetical functions II "
                    + "(1987), DOI 10.1007/BF01951008."))),
            DescribeRole.Theorem))));
}
