using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class ExponentialTentEnergyDocument : IScribeDocumentDefinition
{
    private const string ModulePath = "D5/S3/Fourier/Concentration/ExponentialTentEnergy";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exponential weight gives an attained minimum and a cubic lower bound for a nonnegative peak.",
        H("Exponential energy of a tent profile"),
        Blocks(
            Paragraph(Text("Use the weight exp(-2|x|) on the real line. A nonnegative profile f with central value a >= 0 is constrained by f(x) >= a - L|x|, where L > 0. Its energy is the integral of the weight times f(x)^2.")),
            Describe.Lean(DescribeId.Create("sharp-energy-bound"),
                DeclarationHandle.Create(ModulePath + ".sharp_energy_bound"),
                H("Attained minimum for a peak"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let r = a/L. Among profiles satisfying the stated constraints with integrable energy density, the minimum is L^2 (r^2 - r + (1 - exp(-2r))/2). The tent max(a - L|x|, 0) is pointwise minimal and attains the integral. Its energy reduces by evenness to twice the integral over [0,r], which is evaluated with an explicit antiderivative."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cube-le-exponential-energy"),
                DeclarationHandle.Create(ModulePath + ".cube_le_exponential_energy"),
                H("Cubic control of the peak"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same pointwise and integrability conditions, a^3 is at most (3/2) exp(2a/L) L times the energy. On the support of the tent, the exponential is bounded below by exp(-2r). Integrating the square of the tent on that interval gives the cubic term."))),
                DescribeRole.Theorem))));
}
