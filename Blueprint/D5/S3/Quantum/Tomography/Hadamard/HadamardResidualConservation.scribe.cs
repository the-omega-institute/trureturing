using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography.Hadamard;

internal sealed class HadamardResidualConservationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual six-outcome residual conservation sharpens validated MUB sublevel enclosures.",
        H("Hadamard Residual Conservation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hadamard-residual-box-dual"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/Hadamard/HadamardResidualConservation.hadamard_residual_box_dual"),
                H("Balanced endpoint dual for the actual matrix residual"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For H H*=6I and six unit-modulus input coordinates, the six squared-modulus "
                    + "residuals sum to zero. Subtracting any common dual coefficient from the "
                    + "readout row preserves its value. Endpoint products then give lower and upper "
                    + "bounds on every real residual in the given intervals. The matrix conservation "
                    + "law is derived in the proof; rational residuals, a numerical root, and dual "
                    + "optimality are not assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("balanced-hadamard-sublevel-row-enclosure"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/Hadamard/HadamardResidualConservation.balanced_hadamard_sublevel_row_enclosure"),
                H("Asymmetric conserved-residual Newton-row enclosure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The explicit Hadamard residual and its actual Frechet derivative feed the existing "
                    + "SublevelRowEnclosure owner. Applying that theorem to f-f(x) isolates the full "
                    + "directional remainder; the balanced dual supplies the remaining endpoint interval. "
                    + "Interval-expression soundness and complete traversal reflection remain separate "
                    + "obligations. An external checker result is not a premise of this theorem."))),
                DescribeRole.Theorem))));
}
