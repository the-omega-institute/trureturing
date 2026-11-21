using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class ReflectingHeatPhysicalGramianDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The centered inverse of the reflecting heat interpolant gives an upper bound on the physical Gramian.",
        H("The reflecting heat Gramian upper bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("reflecting-heat-physical-inverse-diagonal-upper-bound"),
            DeclarationHandle.Create("D5/S3/Observer/Linear/ReflectingHeatPhysicalGramian.inverse_diagonal_upper_bound"),
            H("Upper bound via a real biorthogonal witness"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For an entire multiplier satisfying the radial half-width and real-axis "
                    + "envelope bounds, divide the centered inverse density by the nonzero "
                    + "value of the interpolant at the target node before taking its real part. "
                    + "Under the affine time change the density is supported on the physical "
                    + "interval of length L/n². The Jacobian and the target first-cell weight "
                    + "normalize its moments to the Kronecker delta across all positive modes.")),
                Paragraph(Text(
                    "The physical L² norm is bounded by the angular real-axis L² norm of the "
                    + "interpolant times n exp(q_j L/2) divided by the target first-cell weight, "
                    + "the modulus of the target nodal value, and sqrt(2π). The time change "
                    + "contributes n and the conversion from angular frequency to cycles "
                    + "contributes 1/sqrt(2π).")),
                Paragraph(Text(
                    "The synthesis of the inverse Gramian column has squared norm equal to "
                    + "the target inverse diagonal. Its inner product with the witness equals "
                    + "the same diagonal by the moment equations. Cauchy–Schwarz bounds the "
                    + "square root of the diagonal by the norm of the witness."))),
            DescribeRole.Theorem))));
}
