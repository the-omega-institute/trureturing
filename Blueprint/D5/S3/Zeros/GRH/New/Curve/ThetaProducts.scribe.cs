using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Curve;

internal sealed class ThetaProductsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Theta Products", H("Theta Products"),
        Blocks(
            Paragraph(Text("Theta products along tight frames: integral up to one exponential coupling partner places.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Curve/ThetaProducts.thetaProducts_normal_form"),
                H("thetaProducts_normal_form"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For (p/d) ≠ 1, some ϖ, π with |ϖ| = p^{−ρ_p} (ρ_p = nonsplitWeight), |π| = p^{((p/d)−1)/2} serve all r ≤ 1 and Θ in Parameters.thetaProducts (δ = 1): IsIntegralOnNullCone holds for each B, with couplings j ≤ log_p B, j odd or p = d. If (p/d) = −1 and r = 1, Θ(ϖz) = exp(κΨ)V with |κ| = p^{1−1/(p−1)}, Ψ, V integral, Ψ(0) = 0, and ∂_xΨ has unit coefficients exactly at the z_y^{p^j}, j odd, −p^j y = x.")))))));
}
