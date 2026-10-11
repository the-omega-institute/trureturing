using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class FilteredDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "This module supplies the indicated step in the unbounded solidification construction.",
        H("Filtered"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-filtered-preservesfilteredcolimits-ihom-p-of-pointwise-hom"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/Filtered.preservesFilteredColimits_ihom_P_of_pointwise_hom"),
                H("preserves Filtered Colimits ihom P of pointwise hom"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reduction from pointwise ordinary hom preservation to internal hom preservation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-filtered-preservesfilteredcolimits-ihom-p-scaffold"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/Filtered.preservesFilteredColimits_ihom_P_scaffold"),
                H("preserves Filtered Colimits ihom P scaffold"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Final scaffold for the target lemma in `LightSolid.lean`."))),
                DescribeRole.Theorem))));
}
