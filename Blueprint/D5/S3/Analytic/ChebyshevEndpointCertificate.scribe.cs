using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class ChebyshevEndpointCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/ChebyshevEndpointCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A shifted Chebyshev filter gives a dimension-free endpoint certificate from actual finite noisy moments.",
        H("Chebyshev Endpoint Certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("chebyshev-endpoint-noisy-moment-certificate"),
                DeclarationHandle.Create(Prefix + "noisy_moment_endpoint_certificate"),
                H("Quadratic endpoint amplification with an explicit noise cost"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For two nonnegative normalized finite spectra, the first supported above a and the second in [a,b], an atom at x at least b of weight at least eta obeys 2 eta n^2 (x-b) <= (b-a) [2(1-eta)+epsilon Q^n], where Q=2(2+a+b)/(b-a)+1, whenever their actual Prony moments through degree n differ by at most epsilon. The proof constructs the affine Chebyshev filter, derives its n^2 exterior growth from a first-difference induction, and propagates the raw-moment noise budget through the recurrence of a modified linear functional. No polynomial certificate, spectral separation, or mode-count bound is assumed. The observation-horizon minimax law is an ordinary consumer in the theory and is not asserted by this Lean theorem."))),
                DescribeRole.Theorem))));
}
