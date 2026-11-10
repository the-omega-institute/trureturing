using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Lieb;

internal sealed class QuadraticPerspectiveDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint convexity of the finite-dimensional quadratic operator perspective.",
        H("QuadraticPerspective"), Blocks(
            Describe.Lean(
                DescribeId.Create("quadratic-perspective-joint-convexity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Lieb/QuadraticPerspective.joint_convexity"),
                H("Quadratic perspective joint convexity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For finite complex matrices, Hermitian A₀ and A₁ and "
                            + "positive-definite B₀ and B₁ satisfy the Loewner-order "
                            + "inequality Aₜ Bₜ⁻¹ Aₜ ≤ t A₀ B₀⁻¹ A₀ + "
                            + "(1-t) A₁ B₁⁻¹ A₁ for every t in [0,1], where "
                            + "Aₜ and Bₜ are the corresponding affine mixtures. The "
                            + "proof averages two positive block matrices and applies "
                            + "the Schur-complement characterization. No commutativity "
                            + "assumption is used."))),
                DescribeRole.Theorem))));
}
