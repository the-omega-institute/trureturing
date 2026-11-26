using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord.JointAxis;

internal sealed class RationalClockDependenceDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/Robin/PriceRecord/JointAxis/RationalClockDependence";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dependent Robin clock bases admit a coprime common base and a quantitative logarithmic gap.",
        H("Rational dependence of Robin clock labels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("clock-dependent-iff-common-base"),
                DeclarationHandle.Create(Gid + ".clock_dependent_iff_common_base"),
                H("Common-base classification and numerator divisibility"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For natural labels h, p and q with 0 < h, 2h ≤ p and q ≤ 3h, "
                        + "put α = 3p/(p + q) and β = 2p/(p + h) in the rationals. "
                        + "The bases are dependent exactly when α = tᴬ and β = tᴮ for a rational "
                        + "t > 1 and positive coprime A and B, with the B-th power of the reduced "
                        + "numerator of t dividing 2p.")),
                    Paragraph(Text("Cancel the common factor of the exponents and take a common rational "
                        + "root using Bézout's identity. Clearing the second denominator then gives "
                        + "the divisor bound by coprimality of the reduced numerator and denominator."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dependent-clock-abs-lower"),
                DeclarationHandle.Create(Gid + ".dependent_clock_abs_lower"),
                H("Lower bound for a nonzero dependent form"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Under the same label bounds, a nonzero dependent form Ω has "
                        + "|Ω| ≥ log(4/3) log(2) / log(2p). The second base is at least 4/3, and "
                        + "numerator divisibility gives B log(2) ≤ log(2p). The form is the product "
                        + "of log(t) and the nonzero integer hA − qB."))),
                DescribeRole.Theorem))));
}
