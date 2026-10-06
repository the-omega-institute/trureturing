using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class SingularSolidDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "This module supplies the indicated step in the unbounded solidification construction.",
        H("Singular Solid"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-singularsolid-singularchaingroup-issolid"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/SingularSolid.singularChainGroup_isSolid"),
                H("singular Chain Group is Solid"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Discrete integral singular chain groups are solid in every homological degree, for every topological space."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-singularsolid-singularchainscomplex-issolid"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/SingularSolid.singularChainsComplex_isSolid"),
                H("singular Chains Complex is Solid"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every term of the exact protected reindexed singular-chain complex is solid."))),
                DescribeRole.Theorem))));
}
