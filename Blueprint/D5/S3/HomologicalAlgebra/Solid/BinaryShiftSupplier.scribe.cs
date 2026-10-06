using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class BinaryShiftSupplierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "This module supplies the indicated step in the unbounded solidification construction.",
        H("Binary Shift Supplier"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-binaryshiftsupplier-pbinaryright-shift"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/BinaryShiftSupplier.PbinaryRight_shift"),
                H("Pbinary Right shift"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. This module supplies the indicated step in the unbounded solidification construction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-binaryshiftsupplier-binary-p-subdivision"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/BinaryShiftSupplier.binary_P_subdivision"),
                H("binary P subdivision"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. This module supplies the indicated step in the unbounded solidification construction."))),
                DescribeRole.Theorem))));
}
