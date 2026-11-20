using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PrincipalTrianglePhaseBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Principal Gram data and cross-overlap dominance give a quadratic error penalty.",
        H("Near-real phase bound for principal quantum recovery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rt-principal-cross-dominance-phase"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Recovery/PrincipalTrianglePhaseBound.triangle_imag_of_cross_dominance"),
                H("Phase obstruction from cross-entry dominance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The positive Gram completion fills defects only inside each two-dimensional fibre and "
                    + "preserves every cross entry. If the first record does not exceed the second in "
                    + "cross-entry modulus, a matrix-unit error below one quarter forces a quantitative "
                    + "non-real triangle in the second record. A positive correlation quotient with unit "
                    + "diagonal implies, but is not needed to state, this modulus dominance."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rt-principal-near-real-quadratic"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Recovery/PrincipalTrianglePhaseBound.near_real_error_lower_of_cross_dominance"),
                H("Quadratic penalty for near-real triangles"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If all eight absolute triangle imaginary parts are at most eta, the matrix-unit error "
                    + "is at least one quarter minus 128 eta squared over 27. The constant is a closed-form "
                    + "corollary of the phase bound, not a claimed optimum for unrestricted quantum channels."))),
                DescribeRole.Theorem))));
}
