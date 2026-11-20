using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class RadialVolterraDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite interval mass bounds control a scalar Volterra system with terminal data at infinity.",
        H("Radial Volterra bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("radial-volterra-norm-bounds"),
                DeclarationHandle.Create("D5/S3/Analytic/RadialVolterra.norm_bounds"),
                H("Uniform amplitude and deviation bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On the positive half-line, let eta have derivative p with Re p ≥ 0, and let "
                    + "F and G solve F′ = p G and G′ = 2ν p G + q F with terminal limits one and zero. "
                    + "If the norm of q is bounded by a continuous nonnegative Q whose integral on "
                    + "each finite positive interval is at most V, with 0 ≤ V < ν, then "
                    + "|F(r)| ≤ ν/(ν−V) and |F(r)−1| ≤ V/(ν−V) for every r > 0. "
                    + "For each r the exponential integrating factor bounds the kernel by 1/ν. "
                    + "The terminal data and the mass bound control the error by V/ν times "
                    + "the supremum of |F| on the ray from r. Solving the supremum inequality "
                    + "gives both bounds."))),
                DescribeRole.Theorem))));
}
