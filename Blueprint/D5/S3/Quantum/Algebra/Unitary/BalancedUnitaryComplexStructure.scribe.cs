using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.Unitary;

internal sealed class BalancedUnitaryComplexStructureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Balanced relative products give complex structures and Hermitian involutions.",
        H("Balanced Unitary Complex Structure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create(
                    "balanced-structure-relative-complex-structure"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure."
                    + "relativeComplexStructure"),
                H("Relative mixed product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For finite complex square matrices A and B, the relative complex "
                    + "structure is twice A times the adjoint of B."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "balanced-structure-relative-complex-structure-is-skew-adjoint"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure."
                    + "relativeComplexStructure_is_skewAdjoint"),
                H("Skew-adjoint relative product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If A times the adjoint of B plus B times the adjoint of A is zero, "
                    + "the relative complex structure is skew-adjoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "balanced-structure-relative-complex-structure-mul-conj-transpose"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure."
                    + "relativeComplexStructure_mul_conjTranspose"),
                H("Right unitarity of the relative product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If A times its adjoint and the adjoint of B times B both equal half "
                    + "the identity, the relative complex structure times its adjoint is "
                    + "the identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "balanced-structure-relative-complex-structure-conj-transpose-mul"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure."
                    + "relativeComplexStructure_conjTranspose_mul"),
                H("Left unitarity of the relative product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If the adjoint of A times A and B times its adjoint both equal half "
                    + "the identity, the adjoint of the relative complex structure times "
                    + "that structure is the identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "balanced-structure-square-eq-neg-one-of-skew-adjoint-unitary"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure."
                    + "square_eq_neg_one_of_skewAdjoint_unitary"),
                H("Square of a skew-adjoint unitary matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A skew-adjoint complex square matrix whose product with its adjoint "
                    + "is the identity has square equal to minus the identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "balanced-structure-relative-complex-structure-square"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure."
                    + "relativeComplexStructure_square"),
                H("Complex structure equation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Cross cancellation, right half-normalization of A and left "
                    + "half-normalization of B imply that the relative complex structure "
                    + "squares to minus the identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "balanced-structure-relative-involution"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure."
                    + "relativeInvolution"),
                H("Induced involution matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The relative involution is the relative complex structure "
                    + "multiplied by the complex scalar i."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "balanced-structure-relative-involution-is-hermitian"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure."
                    + "relativeInvolution_isHermitian"),
                H("Hermitian induced matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Cross cancellation implies that the relative involution equals its "
                    + "adjoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "balanced-structure-relative-involution-square"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/Unitary/BalancedUnitaryComplexStructure."
                    + "relativeInvolution_square"),
                H("Involution equation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Cross cancellation, right half-normalization of A and left "
                    + "half-normalization of B imply that the relative involution squares "
                    + "to the identity."))),
                DescribeRole.Theorem))));
}
