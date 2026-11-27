using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.DiscreteSeries;

internal sealed class GaussianShapeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian Shape", H("Gaussian Shape"),
        Blocks(
            Paragraph(Text("Near 1 the coefficient is explicit phase times real factor, uniform error.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/DiscreteSeries/GaussianShape.dsCoeff_gaussian_shape"),
                H("dsCoeff_gaussian_shape"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Gaussian shape: let l = 2λ have gap 500n³, |l_a| ≤ L, T ≥ max(1, n², n² log(n+L+1)), 10¹²δT ≤ 1, ‖g−1‖ ≤ δ (Frobenius). Then |ψ_λ(g)/exp tr(diag(Λ) log g) − κ| ≤ κ/10 + e^{−100T} for some κ∈[0,1], log g = logOneAdd(g−1), Λ = HCParam.lowestKType.")))))));
}
