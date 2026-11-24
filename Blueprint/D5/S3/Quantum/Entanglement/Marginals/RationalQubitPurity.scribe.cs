using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Marginals;

internal sealed class RationalQubitPurityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An arithmetic criterion for a pure two-qubit extension with rational matrix entries.",
        H("Rational pure extensions of qubit marginals"),
        Blocks(
            Describe.Lean(DescribeId.Create("rational-qubit-purity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Entanglement/Marginals/RationalQubitPurity.rational_qubit_purity_iff"),
                H("Rational pure qubit extensions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A rational pure joint state exists exactly when both two-by-two "
                        + "marginals are positive semidefinite, rational and trace one, their "
                        + "determinants agree, and the common determinant is a sum of two rational squares.")),
                    Paragraph(Text(
                        "A nonzero column of the pure density supplies rational projective "
                        + "amplitudes. The determinant of their two-by-two array, divided by the "
                        + "diagonal entry of that column, has squared modulus equal to the marginal "
                        + "determinant.")),
                    Paragraph(Text(
                        "For sufficiency, transpose the right marginal. The two Hermitian matrices "
                        + "are intertwined by a rational Hermitian matrix whose square is a positive "
                        + "scalar multiple of the identity. Shift the left matrix by a scalar of "
                        + "the required squared modulus and multiply by the intertwiner. "
                        + "Cayley–Hamilton reduces its Gram products to the two required marginals "
                        + "with the same rational scale. Dividing the outer product by that scale "
                        + "gives the normalized state with rational matrix entries."))),
                DescribeRole.Theorem))));
}
