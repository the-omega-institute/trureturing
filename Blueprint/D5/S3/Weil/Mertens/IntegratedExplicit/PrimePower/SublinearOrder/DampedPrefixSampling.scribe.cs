using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class DampedPrefixSamplingDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/DampedPrefixSampling";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Damped spectral sums of signed prefixes",
        H("Local square-mass estimates on the negative half-line"),
        Blocks(
        Describe.Lean(DescribeId.Create("damped-mode-integral-square-mass"),
            DeclarationHandle.Create(Owner + ".exists_damped_mode_integral_le_square_mass"),
            H("Exponentially weighted spectral integral"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For each integer j≥0, integrate on the cell (−j−1,−j]. The exponential weight exp(v/2) is "
                    + "at most exp(−j/2) there.")),
                Paragraph(Text("The cell lies in the interval of radius one about −j. Apply the local spectral integral "
                    + "estimate with the same square-summable bin majorant on every cell, then sum the geometric "
                    + "weights."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("damped-reciprocal-sum-square-mass"),
            DeclarationHandle.Create(Owner + ".exists_damped_reciprocal_sum_le_square_mass"),
            H("A reciprocal spectral sum from the signed degree prefix"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Write A(t) for the sum of a(n) over those n in J with t≤v(n). For z=1/2+iγ, integrate "
                    + "A(t) exp(zt) on t≤0. Each v(n)≤0 contributes a(n) exp(zv(n))/z, including v(n)=0.")),
                Paragraph(Text("Summing the finitely many spectral coefficients inside the integral gives the same prefix "
                    + "against one finite sum of phase modes. Bound the prefix by P and apply the weighted "
                    + "spectral integral estimate. The frequency bin masses count the coefficients of every "
                    + "occurrence."))),
            DescribeRole.Theorem))));
}
