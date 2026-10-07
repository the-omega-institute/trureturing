using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid.Supplier;

internal sealed class FreeAugmentationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "This module supplies the indicated step in the unbounded solidification construction.",
        H("Free Augmentation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-freeaugmentation-freeaugmentationsection-comp"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/Supplier/FreeAugmentation.freeAugmentationSection_comp"),
                H("free Augmentation Section comp"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. This module supplies the indicated step in the unbounded solidification construction."))),
                DescribeRole.Theorem))));
}
