using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class NullDiamondWeakBoundary4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary4D.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Regulated shell squares and the smeared bulk correction.",
        H("Regulation on the null cone"),
        Blocks(
            Entry("shell-amplitude", "shellAmplitude", "Shell amplitude",
                "Integrate the affine radius times the radial derivative against the momentum plane wave over the affine interval and round sphere.", DescribeRole.Definition),
            Entry("regulated-square", "regulatedShellQuad", "Regulated shell square",
                "Integrate four times the shell density multiplied by the exponential energy damping and the squared modulus of the shell amplitude.", DescribeRole.Definition),
            Entry("nonnegative-square", "regulatedShellQuad_nonneg", "Nonnegativity",
                "The shell density, exponential damping, and square are nonnegative for every real mass and regulator."),
            Entry("bulk-pairing", "regulatedShellQuad_eq_bulk", "Regulated bulk pairing",
                "At a positive regulator the shell square equals the real part of the double boundary pairing with the regulated bulk kernel. The damping and bounded affine derivative give the integrable majorant for Fubini."),
            Entry("shell-difference-limit", "regulatedShellQuad_difference_limit", "Limit of the shell difference",
                "The massive regulated shell square minus its massless counterpart converges to the real part of four times the smeared position-space correction."),
            Entry("massless-cap", "bulkU_zero_cap", "Massless angular denominator",
                "Multiplying the zero-mass bulk kernel by four times the product of the two affine radii leaves the cap denominator with prefactor one divided by twice pi squared."),
            Entry("massless-boundary", "massless_boundary_limit", "Massless weak boundary",
                "As the positive regulator tends to zero, the shell square converges to the real quadratic form of the massless multiplier on the weighted Fourier embedding. Subtracting the coincident angular value leaves a dominated integral that vanishes by radial cancellation. The cap primitive supplies the logarithmic form."),
            Entry("massive-boundary", "massive_boundary_limit", "Massive weak boundary",
                "For positive mass the limiting quadratic form includes the existing correction operator. The bulk difference has an integrable angular logarithm after smearing. Two radial integrations by parts and Fourier inversion identify it with the operator defined by the weighted correction kernel."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}

