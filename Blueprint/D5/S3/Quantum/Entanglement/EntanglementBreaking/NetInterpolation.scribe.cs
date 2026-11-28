using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EntanglementBreaking;

internal sealed class NetInterpolationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bilinear and quadratic interpolation of finite net estimates.",
        H("Interpolation from finite nets"),
        Blocks(
            Describe.Lean(DescribeId.Create("eb-netinterpolation-exists-schmidt-bilinear-net"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/NetInterpolation.exists_schmidt_bilinear_net"),
                H("Bilinear net for bounded Schmidt rank"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Approximation of each factor yields two error terms controlled by the restricted bilinear bound. The net radius allows these errors to be absorbed into that bound."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eb-netinterpolation-exists-full-sphere-quadratic-net"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/NetInterpolation.exists_full_sphere_quadratic_net"),
                H("Quadratic net controls the Hermitian operator norm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Approximate a unit vector on both sides of its quadratic form. Hermiticity relates the supremum of the absolute quadratic form to the operator norm."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eb-netinterpolation-coeffvector"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/NetInterpolation.coeffVector"),
                H("Coeff vector"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Turn a coefficient matrix into the Euclidean vector with the same entries, indexed by the product of the row and column types."))),
                DescribeRole.Definition))));
}
