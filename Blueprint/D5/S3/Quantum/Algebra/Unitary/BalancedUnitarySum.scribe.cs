using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.Unitary;

internal sealed class BalancedUnitarySumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Balanced unitary summands have cancelling cross terms and a skew-adjoint relative product.",
        H("Balanced Unitary Sum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("half-identity-normalization"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/Unitary/BalancedUnitarySum.halfIdentity"),
                H("Half identity normalization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The squared normalization carried by each summand in a balanced unitary sum."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("balanced-summands-cross-terms-cancel"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/Unitary/BalancedUnitarySum.crossTerms_eq_zero"),
                H("Balanced summands have zero mixed Gram sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If S = A + B is unitary and both summands have right Gram matrix I / 2, the mixed Gram terms cancel exactly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("second-cross-term-is-negative-first"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/Unitary/BalancedUnitarySum.secondCross_eq_neg_first"),
                H("The second mixed product is the negative of the first"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Cross cancellation says that one mixed product is the negative adjoint of the other."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("relative-cross-product-skew-adjoint"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/Unitary/BalancedUnitarySum.crossProduct_is_skewAdjoint"),
                H("The relative cross product is skew-adjoint"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The relative cross product of a balanced unitary sum is skew-adjoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("balanced-sum-skew-adjoint-conclusion"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/Unitary/BalancedUnitarySum.crossProduct_is_skewAdjoint_of_balanced_sum"),
                H("Balanced normalization gives the skew-adjoint conclusion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This direct consumer theorem combines balanced normalization with the skew-adjoint conclusion."))),
                DescribeRole.Theorem))));
}
