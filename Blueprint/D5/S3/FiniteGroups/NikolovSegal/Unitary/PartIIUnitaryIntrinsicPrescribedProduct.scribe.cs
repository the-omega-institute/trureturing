using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class PartIIUnitaryIntrinsicPrescribedProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The diagonal and field components define genuine automorphisms of the literal determinant-one Hermitian SU carrier. Steinberg commutation proves inverse closure. Positive-U and negative-L value products retain q/e, uniform constants before all fields/ranks>=6 above the field cutoff and one right-inner correction before all targets in the respective actual subgroups.",
        H("Part IIUnitary Intrinsic Prescribed Product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryintrinsicprescribedproduct-action"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryIntrinsicPrescribedProduct.action"),
                H("action"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual prescribed D/Phi automorphism of the LITERAL SU carrier. Its inverse closure is derived from the actual Steinberg commutation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryintrinsicprescribedproduct-actual-action-entry"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryIntrinsicPrescribedProduct.actual_action_entry"),
                H("actual action entry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized actual action entry statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryintrinsicprescribedproduct-actual-uniform-intrinsic-positive-q-over-e-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryIntrinsicPrescribedProduct.actual_uniform_intrinsic_positive_q_over_e_product"),
                H("actual uniform intrinsic positive q over e product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Original scalar supplier correction convention, intrinsically on SU, for ALL positive-U targets. N,C precede all fields/ranks/tuples; ONE y precedes ALL targets. This is honest U coverage, not full scalar coverage."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryintrinsicprescribedproduct-actual-uniform-intrinsic-negative-q-over-e-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryIntrinsicPrescribedProduct.actual_uniform_intrinsic_negative_q_over_e_product"),
                H("actual uniform intrinsic negative q over e product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Original scalar supplier correction convention, intrinsically on SU, for ALL negative-U targets. N,C precede all fields/ranks/tuples; ONE y precedes ALL targets. This is honest lower-U coverage, not full scalar coverage."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
