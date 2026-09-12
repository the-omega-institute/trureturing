using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography.Cayley;

internal sealed class CayleyHadamardDifferentialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual signed-Cayley measurement residual has an explicit directional derivative and a balanced scalar enclosure.",
        H("Actual Cayley Residual Differential"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("signed-cayley-actual-residual-derivative"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/Cayley/CayleyHadamardDifferential.signed_cayley_hadamard_residual_hasDerivAt"),
                H("The displayed residual derivative is derived from the actual matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an arbitrary complex six-by-six matrix, the source differentiates the real and imaginary signed-Cayley coordinates along an affine real segment. "
                    + "Finite complex matrix multiplication and the squared-modulus product rule give the displayed scalar directional derivative. "
                    + "No supplied Jacobian correctness assumption is used. The five-coordinate dephased chart is obtained by fixing the first coordinate. "
                    + "This theorem does not itself certify interval arithmetic or a full Frechet-derivative implementation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signed-cayley-balanced-sublevel-row"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/Cayley/CayleyHadamardDifferential.signed_cayley_balanced_sublevel_row_enclosure"),
                H("The derived directional derivative yields a balanced row enclosure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The source reuses HadamardResidualConservation for the six-outcome residual dual and Mathlib's scalar mean-value inequality on the complete closed segment. "
                    + "The actual residual derivative is the preceding theorem, not an input oracle. Numerical bounds on that formula, the seed Gram identity and the endpoint residual intervals remain explicit. "
                    + "The complete derivative remainder and the small-residual term are both retained. A successful external trace does not supply these Lean proof inputs."))),
                DescribeRole.Theorem))));
}
