using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid.Supplier;

internal sealed class ProfiniteCoverDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "This module supplies the indicated step in the unbounded solidification construction.",
        H("Profinite Cover"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-profinitecover-profinitecover-free-epi"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/Supplier/ProfiniteCover.profiniteCover_free_epi"),
                H("profinite Cover free epi"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same covering augmentation is epimorphic for the protected free functor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-profinitecover-binaryintervalcover-free-epi"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/Supplier/ProfiniteCover.binaryIntervalCover_free_epi"),
                H("binary Interval Cover free epi"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Its free augmentation onto the actual free condensed interval object."))),
                DescribeRole.Theorem))));
}
