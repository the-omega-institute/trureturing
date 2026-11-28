using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.DiscreteSeries;

internal sealed class BesselExistenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bessel Existence", H("Bessel Existence"),
        Blocks(
            Paragraph(Text("Record tying a Bessel system to its weight, degree and discrete series projector. Point of controlled size, from Lagrange weights, where the Bessel phases cancel. A discrete series Bessel function explicitly large at a point where phases cancel.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/DiscreteSeries/BesselExistence.exists_isBesselFunction"),
                H("exists_isBesselFunction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For continuous rep with ⟨v, rep(·)v⟩ = ψ_u, l HCParam.HasLargeGap, b ≥ 16, phase σ − σ̄ at x, ν right Haar on Shape.besselGraph, ν(‖p⁻¹x⁻¹sxp − 1‖ ≤ 1) ≤ bⁿ|∫θ dν|: some Bessel W = W∗(deg·ψ) has W(x) ≠ 0, ‖W(y)‖ ≤ ∫|ψ(x⁻¹sy)|dν, ∫(2/‖p⁻¹x⁻¹syp‖)^N dν ≤ b^{N+n}‖W(x)‖ for all y, N = 8·rank²+1; θ = HCParam.laplaceIntegrand, σ = simpleRootSum.")))))));
}
