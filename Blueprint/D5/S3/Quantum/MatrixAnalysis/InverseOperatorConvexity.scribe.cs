using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.MatrixAnalysis;

internal sealed class InverseOperatorConvexityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite positive-definite complex matrices inherit the operator convexity of inversion.",
        H("Inverse Operator Convexity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pos-def-weighted-inverse-le"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/MatrixAnalysis/InverseOperatorConvexity.posDef_weighted_inverse_le"),
                H("Weighted inverse inequality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite index type and positive-definite complex matrices A and B, "
                            + "nonnegative real weights a and b with a+b=1 satisfy "
                            + "(aA+bB)⁻¹ ≤ aA⁻¹+bB⁻¹ in the matrix order. The proof transports "
                            + "Mathlib's C⋆-algebra convexity theorem from strict positivity and "
                            + "Ring.inverse to Matrix.PosDef and the nonsingular matrix inverse; "
                            + "A and B need not commute. This is the finite matrix bridge used by "
                            + "trace and divergence constructions."))),
                DescribeRole.Theorem))));
}
