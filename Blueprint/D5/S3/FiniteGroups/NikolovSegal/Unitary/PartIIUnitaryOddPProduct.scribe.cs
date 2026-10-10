using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class PartIIUnitaryOddPProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual part iiunitary odd pproduct supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Part IIUnitary Odd PProduct"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryoddpproduct-actual-odd-p-vector-two-batch"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryOddPProduct.actual_odd_P_vector_two_batch"),
                H("actual odd P vector two batch"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Genuine vector-quotient VALUE reconstruction in TWO ordered batches. The fixed-field torus corrections precede all vector targets, witnesses are actual positive-unitary P matrices, and the central cross terms are retained as the actual unitary residual, rather than assumed covered."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryoddpproduct-actual-odd-p-field-four-batch"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryOddPProduct.actual_odd_P_field_four_batch"),
                H("actual odd P field four batch"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Full genuine odd-dimensional P FIELD PRODUCT, PartII pp271–272. All FOUR fixed-field inner correction batches precede ALL true P vector/central targets. The actual quotient witnesses, trace lifts, noncommutative residual, positive/unitary constraints and original positive divisor powers are consumed; no coverage/scalar oracle remains."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryoddpproduct-actual-uniform-odd-p-field-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryOddPProduct.actual_uniform_odd_P_field_product"),
                H("actual uniform odd P field product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All odd ranks and fields: chosen N(q),C(q) precede every FIELD tuple; actual determinant-one diagonal UNITARY h precedes every true P target. Ordered exact-length original positive-divisor commutator VALUES."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
