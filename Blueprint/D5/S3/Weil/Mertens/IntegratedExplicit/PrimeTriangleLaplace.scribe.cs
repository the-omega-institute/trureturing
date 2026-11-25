using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class PrimeTriangleLaplaceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The centered triangular Mangoldt sum retains the pole at each zeta zero in the critical strip.",
        H("The Laplace transform of the prime triangle"),
        Blocks(Describe.Lean(
            DescribeId.Create("hinge-transform-integral-and-zero-residues"),
            DeclarationHandle.Create(
                "D5/S3/Weil/Mertens/IntegratedExplicit/PrimeTriangleLaplace.hingeTransform_integral_and_zero_residues"),
            H("Absolute convergence and nonzero residues"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "In logarithmic coordinates, the centered Mangoldt triangle is the combination "
                    + "U(4 exp t) − 3U(2 exp t) + 2U(exp t). Its Laplace integral converges absolutely "
                    + "for Re(s) > 1. A shift by h multiplies the transform with its initial interval "
                    + "removed by exp(sh). Summing with coefficients 1, −3, and 2 gives "
                    + "(2^s − 1)(2^s − 2) times the original transform, minus an entire correction.")),
                Paragraph(Text(
                    "For a zero ρ with 0 < Re(ρ) < 1, the magnitude of 2^ρ lies strictly between 1 and 2. "
                    + "The multiplier therefore preserves the pole, giving residue "
                    + "(2^ρ − 1)(2^ρ − 2) times the multiplicity divided by ρ(1 − ρ)."))),
            DescribeRole.Theorem))));
}
