using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSUniformHardCoreFoldCurvatureDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreFoldCurvature";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hard-core energy and the curvature of the coherence fold",
        H("Hard-core energy and the curvature of the coherence fold"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcorefoldcurvature-coherence-curvature-on-regular-level"),
                DeclarationHandle.Create(Module + ".coherence_curvature_on_regular_level"),
                H("Strict coherence curvature on a regular level"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/StatisticalMechanics/lesanovsky2012constrainedspinchain")),
                Blocks(
                    Paragraph(Text("At length n ≥ 7 the affine energy readout is stationary at the witness. Its second derivative in the regular null direction is strictly positive by the Dirichlet energy of the tangent variation. On any twice differentiable curve through the witness tangent to this direction and with locally constant regular readings, the real 00,01 coherence has strictly negative second derivative."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcorefoldcurvature-forbidden-corner-hessian-zero"),
                DeclarationHandle.Create(Module + ".forbidden_corner_hessian_zero"),
                H("Vanishing second derivative of the forbidden population"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/StatisticalMechanics/lesanovsky2012constrainedspinchain")),
                Blocks(
                    Paragraph(Text("The normalized 11,11 population has zero second derivative on the same null line. This allows a higher-order separation after the coherence has supplied the fold."))),
                DescribeRole.Theorem))));
}
