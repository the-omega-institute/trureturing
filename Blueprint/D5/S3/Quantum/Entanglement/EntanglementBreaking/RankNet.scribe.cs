using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EntanglementBreaking;

internal sealed class RankNetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite nets for complex coefficient matrices of bounded rank.",
        H("Nets of fixed-rank coefficient matrices"),
        Blocks(
            Describe.Lean(DescribeId.Create("eb-ranknet-exists-rank-sphere-net"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/RankNet.exists_rank_sphere_net"),
                H("Finite net on the rank-bounded unit sphere"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Factor each rank-at-most-k coefficient matrix with unit Frobenius norm into an isometry with k columns and a unit Frobenius factor. The product of an operator norm net and a Frobenius norm net gives the approximants. Both factor nets lie within their respective sets."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eb-ranknet-rectangularopnorm"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/RankNet.rectangularOpNorm"),
                H("Rectangular op norm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Take the Euclidean operator norm of the linear map given by multiplication by the rectangular complex matrix."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("eb-ranknet-exists-stiefel-net"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/RankNet.exists_stiefel_net"),
                H("Exists stiefel net"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("There is an internal one-eighth net for the complex isometries in the rectangular operator norm, of cardinality at most seventeen raised to the real ambient dimension."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eb-ranknet-exists-frobenius-sphere-net"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/RankNet.exists_frobenius_sphere_net"),
                H("Exists frobenius sphere net"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("There is an internal one-eighth net for the complex Frobenius unit sphere, of cardinality at most seventeen raised to the real ambient dimension."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eb-ranknet-exists-left-stiefel-factorization"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/RankNet.exists_left_stiefel_factorization"),
                H("Exists left stiefel factorization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("When k is at most d, a d by d coefficient matrix of rank at most k and Frobenius norm one factors as a d by k isometry times a k by d matrix of Frobenius norm one."))),
                DescribeRole.Theorem))));
}
