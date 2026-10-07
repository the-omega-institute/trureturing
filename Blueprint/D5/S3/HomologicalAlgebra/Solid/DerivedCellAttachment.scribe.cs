using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class DerivedCellAttachmentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The simultaneous, arbitrary-size actual cell attachments tested in the unbounded derived category. New proofs, released under Apache 2.0.",
        H("Derived Cell Attachment"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-derivedcellattachment-solidcellsattachment-derivedprecomp-bijective"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/DerivedCellAttachment.solidCellsAttachment_derivedPrecomp_bijective"),
                H("solid Cells Attachment derived Precomp bijective"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Simultaneous attachment of an arbitrary family of the protected cells has a universal derived comparison to each derived-local target."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-derivedcellattachment-solidcellularstep-derivedprecomp-bijective"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/DerivedCellAttachment.solidCellularStep_derivedPrecomp_bijective"),
                H("solid Cellular Step derived Precomp bijective"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual saved attachment step, along all maps from all defining cells, has the proved universal derived comparison."))),
                DescribeRole.Theorem))));
}
