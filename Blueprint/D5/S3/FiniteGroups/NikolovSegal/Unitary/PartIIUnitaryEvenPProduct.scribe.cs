using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class PartIIUnitaryEvenPProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual part iiunitary even pproduct supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Part IIUnitary Even PProduct"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryevenpproduct-actual-skew-two-batch"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryEvenPProduct.actual_skew_two_batch"),
                H("actual skew two batch"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Simultaneous reconstruction of ALL genuine P coordinates. Upper parameters are freely solved, their paired entries are forced by the true involution, and diagonal witnesses lie in the trace-zero line."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryevenpproduct-actual-even-p-two-batch-inner-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryEvenPProduct.actual_even_P_two_batch_inner_product"),
                H("actual even P two batch inner product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual even P VALUE PRODUCT inside the ambient SU(2d+2). Both genuine INNER UNITARY correction batches precede ALL targets; all original positive divisor powers and ordered VALUES are retained."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
