using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaExplicit;

internal sealed class LandauRightVerticalDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaExplicit/LandauRightVertical.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A bound for the right vertical edge of the finite Landau rectangle.",
        H("The right vertical integral"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("landau-right-vertical-integral"),
                DeclarationHandle.Create(Owner + "norm_right_vertical_integral"),
                H("Uniform bound on the moving right edge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let x>1 and V>1 be real and put c=1+1/log(3x). Integrate "
                        + "x^(c+it) times the negative logarithmic derivative of the Riemann "
                        + "zeta function over 1<=t<=V. The norm is bounded by "
                        + "400*(V*log(2x)+x*log(2x)^2).")),
                    Paragraph(Text(
                        "The absolutely summable von Mangoldt series can be integrated "
                        + "term by term. Keep the integer nearest to x under the interval "
                        + "length bound. The coefficient at 1 vanishes. For each other integer "
                        + "in [x/2,2x], the logarithmic frequency gap is at least the distance "
                        + "from x divided by 2x. The reciprocal distances sum to at most four "
                        + "times the harmonic sum through floor(2x).")),
                    Paragraph(Text(
                        "Beyond the comparable interval, the logarithmic frequency gap is at "
                        + "least 1/2. The bound log(n)<=n^a/a with a=(c-1)/2 and the integral "
                        + "test give a coefficient sum of at most 4/(c-1)^2 before the "
                        + "factor x^c. The moving line satisfies x^c<=3x. These bounds apply "
                        + "also at exact resonance and as x decreases to 1.")),
                    Paragraph(Text(
                        "This estimate controls the right edge of the contour. A zero-sum "
                        + "formula additionally requires bounds for the other edges, the "
                        + "residue identity and the passage to arbitrary heights."))),
                DescribeRole.Theorem))));
}
