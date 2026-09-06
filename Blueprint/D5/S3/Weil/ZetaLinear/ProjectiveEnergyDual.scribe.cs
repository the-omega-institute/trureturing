using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaLinear;

internal sealed class ProjectiveEnergyDualDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual projective error has a shifted energy budget, which is consumed by a residual-certified directional readout.",
        H("Projective Energy Dual"),
        Blocks(
            Describe.Lean(DescribeId.Create("shifted-action"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaLinear/ProjectiveEnergyDual.shiftedAction"), H("Actual shifted domain action"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Subtracts a real scalar multiple of the domain embedding from the original action. The domain is unchanged, and no bounded extension is imposed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("shifted-energy"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaLinear/ProjectiveEnergyDual.rayleigh_shifted_energy_bound"), H("Derive the actual shifted error energy"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reuses nonzero overlap, orthogonality and the projective energy identity. The term (lambda-ell)*(1-error squared) is nonnegative, yielding a shifted error energy between zero and U-ell. This energy bound is a conclusion."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("directional-readout"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaLinear/ProjectiveEnergyDual.rayleigh_dual_readout"), H("Actual eigenmode directional certificate"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any candidate-orthogonal trial, proves a nonnegative residual-based coefficient and a squared projective readout error bounded by that coefficient times U-ell. The residual uses the full shifted action, including omitted modes. Actual symmetry, eigenvector and complement coercivity remain explicit inputs."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/ZetaLinear/CoerciveDualCertificate")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/Hankel/ProjectiveRayleighReadout"))]));
}
