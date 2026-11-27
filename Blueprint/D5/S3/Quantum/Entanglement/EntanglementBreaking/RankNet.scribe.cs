using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EntanglementBreaking;

internal sealed class RankNetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        H("Nets of fixed-rank coefficient matrices"),
        Blocks(
            Describe.Lean(DescribeId.Create("eb-ranknet-exists-rank-sphere-net"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/RankNet.exists_rank_sphere_net"),
                H("Finite net on the rank-bounded unit sphere"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Factor each rank-at-most-k coefficient matrix with unit Frobenius norm into an isometry with k columns and a unit Frobenius factor. The product of an operator norm net and a Frobenius norm net gives the approximants. Both factor nets lie within their respective sets."))),
                DescribeRole.Theorem))));
}
