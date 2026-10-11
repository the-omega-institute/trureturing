using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class ChainHomologyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "This module supplies the indicated step in the unbounded solidification construction.",
        H("Chain Homology"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-chainhomology-discreteab-preservesfinitecolimits"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/ChainHomology.discreteAb_preservesFiniteColimits"),
                H("discrete Ab preserves Finite Colimits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. This module supplies the indicated step in the unbounded solidification construction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-chainhomology-singularchainsderivedhomologyiso"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/ChainHomology.singularChainsDerivedHomologyIso"),
                H("singular Chains Derived Homology Iso"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reindexing the discrete integral singular chains computes the protected homology object in every degree `-n`. No CW comparison is assumed or used here."))),
                DescribeRole.Definition))));
}
