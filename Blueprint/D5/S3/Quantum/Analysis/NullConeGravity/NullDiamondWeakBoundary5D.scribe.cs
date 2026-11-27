using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class NullDiamondWeakBoundary5DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary5D.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Regulated shell squares and five-dimensional boundary positivity.",
        H("Regulated shell squares and five-dimensional boundary positivity"),
        Blocks(
            Entry("cone-profile5d", "ConeProfile5D", "Interior cone profiles",
                "Finite sums of separated profiles with smooth compactly supported radial factors and Lipschitz angular factors.", DescribeRole.Definition),
            Entry("profile-embed5d", "profileEmbed5D", "Weighted Fourier embedding",
                "Pass to the logistic radial coordinate and multiply the unitary radial Fourier transform by the square root of the massless symmetric weight.", DescribeRole.Definition),
            Entry("profile-embed5d-dense", "profileEmbed5D_dense", "Density in phase space",
                "The weighted transforms of these profiles are dense in the complex Hilbert space over radial frequency and the round three-sphere."),
            Entry("bulk-u5d-zero", "bulkU5D_zero", "Massless bulk function",
                "For positive real part of the regulator, the massless shell integral equals the reciprocal of eight times pi squared times the principal three-halves power of the separation."),
            Entry("bulk-u5d-difference", "bulkU5D_difference", "Bulk correction",
                "At nonnegative mass and positive real part of the regulator, subtract the massless value from the massive value to obtain the elementary half-integer correction."),
            Entry("shell-amplitude5d", "shellAmplitude5D", "Cone plane-wave amplitude",
                "Integrate the affine profile derivative against the plane wave and the three-halves power of the affine radius.", DescribeRole.Definition),
            Entry("regulated-shell-quad5d", "regulatedShellQuad5D", "Regulated shell square",
                "The squared plane-wave amplitude is integrated against the damped mass-shell density and multiplied by four.", DescribeRole.Definition),
            Entry("regulated-shell-quad5d-nonneg", "regulatedShellQuad5D_nonneg", "Spectral positivity",
                "The shell square is nonnegative."),
            Entry("regulated-shell-quad5d-eq-bulk", "regulatedShellQuad5D_eq_bulk", "Bulk representation",
                "For a positive regulator, Fubini exchanges the two affine pairings and the momentum integral and identifies the result with the real part of the bulk pairing."),
            Entry("massless-boundary-limit-5d", "massless_boundary_limit_5D", "Massless right boundary",
                "The semicircle angular density yields an angularly diagonal logarithmic pairing. The finite part cancels against the compact radial derivatives. The remaining term equals the massless modular covariance."),
            Entry("massive-boundary-limit-5d", "massive_boundary_limit_5D", "Massive right boundary",
                "The massive difference is dominated by the integrable inverse square root of one minus the angular dot product. Two radial integrations by parts and mixed Fourier transformation give the frozen massive correction."),
            Entry("null-b5d-nonneg", "nullB5D_nonneg", "Ambient massive positivity",
                "The positive shell squares converge to the massive covariance on dense profiles. Continuity gives positivity on the entire phase space."),
            Entry("null-n5d-sub-j-nonneg", "nullN5D_sub_J_nonneg", "Reflected covariance",
                "Frequency reflection and complex conjugation fix the massive symmetric correction and reverse the centered multiplier. The reflected covariance is therefore positive."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
