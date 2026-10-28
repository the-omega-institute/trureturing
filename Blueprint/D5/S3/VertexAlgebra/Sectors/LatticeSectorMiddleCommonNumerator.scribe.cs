using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeSectorMiddleCommonNumeratorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LatticeSectorMiddleCommonNumerator", H("LatticeSectorMiddleCommonNumerator"), Blocks(
            Describe.Lean(DescribeId.Create("latticesectormiddlecommonnumerator-crossproductslice"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorMiddleCommonNumerator.crossProductSlice"),
                H("crossProductSlice"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The crossProductSlice coefficient construction uses the displayed signed indices and finite polynomial fibers, with exactly the assumptions of its Lean statement."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latticesectormiddlecommonnumerator-actual-three-field-middle-common-numerator"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorMiddleCommonNumerator.actual_three_field_middle_common_numerator"),
                H("actual_three_field_middle_common_numerator"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite recoupling and the actual Borcherds residue identify the cleared middle channel with the middle substitution of the original common numerator at every signed exponent."))), DescribeRole.Theorem))));
}
