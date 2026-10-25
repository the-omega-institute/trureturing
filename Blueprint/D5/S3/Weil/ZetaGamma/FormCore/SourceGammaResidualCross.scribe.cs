using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class SourceGammaResidualCrossDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete residual L1 norm family pays the original cross-series interchange.",
        H("The actual Gamma residual cross is an absolutely integrable series"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("source-gamma-residual-cross-actual-residual-layer-cross-value"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SourceGammaResidualCross.actual_residual_layer_cross_value"),
                H("Every rational layer includes its actual resonant case"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive a and c and arbitrary complex half-line L1 source u, the real cross of xi^2/[c*(xi^2+c^2)*(xi^2+a^2)] equals the literal Laplace expression. The c=a branch retains both normSq(Laplace(a,u))/(4*a^2) and the negative mixed first moment divided by 2*a. Distinct poles use partial fractions; the resonant branch uses the genuine double-pole kernel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-gamma-residual-cross-actual-residual-reflected-cross-complete-series"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SourceGammaResidualCross.actual_residual_reflected_cross_complete_series"),
                H("The complete reflected residual sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every a>0 and the same actual complex L1 source, W(xi)/(xi^2+a^2) times its reflected Fourier cross is integrable. Its real integral is the HasSum of the complete actual layer values at c_n=n+1/4. The final ActualGammaResidualL1 supplier supplies actual layer integrability, a summable series of their exact norms, and the pointwise bare HasSum. The source Fourier bound gives a summable L1 majorant before integration and taking real parts. At a=5/4,n=1, the row remains (4/25)*normSq(Laplace(5/4,u))-(2/5)*Re(conj(Laplace(5/4,u))*FirstMoment(5/4,u))."))),
                DescribeRole.Theorem))));
}
