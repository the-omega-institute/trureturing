using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaExplicit;

internal sealed class LandauLeftVerticalDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaExplicit/LandauLeftVertical.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An oscillatory estimate on the left edge of the finite Landau rectangle.",
        H("The left vertical integral"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("landau-left-vertical-integral"),
                DeclarationHandle.Create(Owner + "norm_left_vertical_integral"),
                H("Uniform bound on the left edge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For real x>1 and V>=1, integrate x^(-1/4+it) times the negative "
                        + "logarithmic derivative of the Riemann zeta function over 1<=t<=V. "
                        + "The norm is at most x^(-1/4)*(80*(V-1)+20*(1+log(V))/log(x)).")),
                    Paragraph(Text(
                        "The zeta functional equation reflects the zeta term to real part 5/4. "
                        + "The digamma recurrence and Binet bound isolate log(3/4+it). "
                        + "The reflected term, tangent and remaining digamma terms have bounded "
                        + "norm, so their integral costs at most 80*(V-1) before scaling.")),
                    Paragraph(Text(
                        "For the logarithm term, integrate by parts against exp(it*log(x)). "
                        + "The phase primitive has norm 1/log(x) and the logarithm derivative "
                        + "has norm at most 1/t. The endpoints and the integrated derivative "
                        + "give 20*(1+log(V))/log(x).")),
                    Paragraph(Text(
                        "The estimate is unconditional and the second term exhibits the "
                        + "loss as x decreases to 1. The sum over zeros also requires a "
                        + "rectangle residue identity, control of the horizontal edges and "
                        + "a transfer to arbitrary cutoff heights."))),
                DescribeRole.Theorem))));
}
