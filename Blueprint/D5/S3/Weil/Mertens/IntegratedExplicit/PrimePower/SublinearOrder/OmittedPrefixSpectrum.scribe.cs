using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class OmittedPrefixSpectrumDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/OmittedPrefixSpectrum";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The damped degree prefix for the omitted zero spectrum",
        H("Combine signed cancellation before summing low frequencies"),
        Blocks(
        Describe.Lean(DescribeId.Create("signed-low-zeta-occurrences-damped-prefix"),
            DeclarationHandle.Create(Owner + ".signed_low_occurrence_sum_of_damped_prefix"),
            H("Low frequencies of the signed degree sum"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For p≤n≤m use v(n)=u/n−2u/q≤0. Since u≥0, the v(n) decrease with n. The indices with "
                    + "t≤v(n) form an initial interval of degrees. Its signed coefficient sum is the difference "
                    + "of two ordinary prefixes bounded by A.")),
                Paragraph(Text("Under RH the root coefficient is −1/ρ−1/(n−ρ). After extracting the unit phase exp(2iu "
                    + "Im(ρ)/q), the −1/ρ term is the damped reciprocal spectral sum. Its square bin mass uses "
                    + "all actual occurrences and the logarithmic local count.")),
                Paragraph(Text("The second coefficient has modulus at most 3/q because 3≤q and q≤2n. Summing its absolute "
                    + "value over at most q degrees costs a constant times the number of low occurrences."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("signed-omitted-density-damped-prefix"),
            DeclarationHandle.Create(Owner + ".signed_omitted_root_density_of_damped_prefix"),
            H("Uniform omitted-root density with a free frequency cutoff"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Apply the preceding bound to the finite low-frequency part and the square-mass tail "
                    + "estimate to its complement. The finite-to-infinite transfer uses summability for each "
                    + "degree and keeps all analytic multiplicities.")),
                Paragraph(Text("The omitted set consists of 2≤n≤m with m+1≤2n. It includes equality when m+1 is even. The "
                    + "low and high contributions share the normalization exp(−(1/2−1/(m+1))u)."))),
            DescribeRole.Theorem))));
}
