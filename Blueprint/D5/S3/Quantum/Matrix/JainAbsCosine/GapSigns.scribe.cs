using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.JainAbsCosine;

internal sealed class GapSignsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All-real sign identities for Fourier modes and short spectral gaps.",
        H("Exact Fourier signs"), Blocks(
            Describe.Lean(DescribeId.Create("jain-mode-exact-sign"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/JainAbsCosine/GapSigns.modeValue_sign"),
                H("Mode signs from forced roots"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural m,j with 1 at most j at most m, and every real exponent r, the sign of the Fourier mode lambda_j(r) equals the sign of the product of r-2s over 0 at most s less than j. The positive cosine bases give strictly decreasing logarithmic exponents. The coefficient variation count and the j prescribed even roots exhaust the exponential Descartes bound; the constant coefficient is positive."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jain-gap-exact-sign"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/JainAbsCosine/GapSigns.modeValue_gap_sign"),
                H("Signs of short spectral gaps"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural j at least one and d equal to one or two with j+d at most m, and every real r, lambda_j(r)-lambda_(j+d)(r) has the sign of the same product. The sine-product coefficient list has j variations even when intermediate coefficients vanish. Its first coefficient is strictly positive. The common even roots and the exact exponential-sum sign theorem give the identity, with no restriction on primality of the odd order."))),
                DescribeRole.Theorem))));
}
