using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.DiscreteSeries;

internal sealed class TwoFactorSetupDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two Factor Setup", H("Two Factor Setup"),
        Blocks(
            Paragraph(Text("Steep parameters, phase cancellation; integrand is large only near diagonal U(X).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/DiscreteSeries/TwoFactorSetup.exists_near_one"),
                H("exists_near_one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Assume IsTwoFactor, B ≥ 1, 0 < r ≤ 1/100. If j(s) = (g, g') has ‖g−a_g‖²+‖g'−a_{g'}‖² ≤ r² (Frobenius, a the block diagonal part), some t has θ(t) = θ(s), θ = HCParam.laplaceIntegrand, with both components of j(t)−1 of norm ≤ 10r.")))))));
}
