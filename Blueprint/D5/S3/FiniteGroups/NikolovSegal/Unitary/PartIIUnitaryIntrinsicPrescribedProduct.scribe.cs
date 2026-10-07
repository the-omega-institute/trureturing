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
                Blocks(Paragraph(Text("The parameterized actual action entry statement supplies a live step in the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
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
            Paragraph(Text("These parameterized results and their consumed helpers support proofs about actual matrix groups over finite fields. Every displayed Lean statement retains its original hypotheses. This package contains no finite enumeration or benchmark-instance deposit. The source geometry is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239. The proof implementation is repository-derived and no originality claim is made. Bare arbitrary automorphism classification, small-field/tiny-rank coverage for the prescribed products, all-family exhaustion and strong completeness are separate obligations. Escape registration is unfinished under CLAUDE3.9 and issue12291; this is not declared_validated registration.")))));
}
