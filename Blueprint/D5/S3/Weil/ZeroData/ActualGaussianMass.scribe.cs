using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroData;

internal sealed class ActualGaussianMassDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual mass bounds consumed by Gaussian localization.",
        H("Actual mass bounds consumed by Gaussian localization"),
        Blocks(
                Paragraph(Text("The occurrence type is the sigma type of every actual zero index and its finite analytic-multiplicity fiber. The existing actual_sigma_inverse_square_summable is transported through actualOccurrenceEquiv, without removing repeated values or either sign of the ordinate. The actual inverse-square mass bound and firstLiMass_lt_one give total mass less than two.")),
                Paragraph(Text("The existing actual_height_gt_ten supplies occurrence_height. Both norm(rho) and norm(1-rho) are at least abs(im(rho)), so the reciprocal coefficient norm is at most im(rho)^(-2). The existing actualH_bound, with its unchanged Li mass, gives norm(H(y))<=2*exp(max(y,0)); its real part satisfies the same absolute bound.")),
                Paragraph(Text("ActualGaussianZeroSum, ActualGaussianLocalWindow, ActualGaussianDirectTail, ActualGaussianEnvelopeMassBudget and OriginalGaussianIntegralBudgets actually consume these estimates. They are source adapters and quantitative consequences of existing suppliers; no independent admission or newly proved actual-zero mass theorem is claimed.")),
                Paragraph(Text("The only proposed shared-supplier change exposes the existing firstLiMass_lt_one and actual_sigma_inverse_square_summable declarations. Their proof bodies are unchanged. This avoids duplicating inaccessible private mathematics.")))));
}
