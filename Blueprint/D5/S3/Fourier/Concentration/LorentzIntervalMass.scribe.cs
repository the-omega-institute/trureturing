using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class LorentzIntervalMassDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/LorentzIntervalMass";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Centered interval bounds control Lorentz-weighted mass.",
        H("A Lorentz integral bound from centered interval mass"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lorentz-mass-upper"),
                DeclarationHandle.Create(Owner + ".lorentz_mass_upper"),
                H("Integrating the centered interval bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let K(x) = 4/(4+x²) be integrable against a positive measure. If the mass of [-r,r] is at most 2ρr+B for every r ≥ 0, then the integral of K is at most 2πρ+B.")),
                    Paragraph(Text("For 0 < u ≤ 1, the superlevel set of K at u is the closed interval of radius 2√(1/u−1). Its mass is bounded by ρ times its Lebesgue length plus B. Integrating in u gives the result, since K has Lebesgue integral 2π and the levels lie in an interval of length one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lorentz-sum-upper"),
                DeclarationHandle.Create(Owner + ".lorentz_sum_upper"),
                H("The bound for weighted finite configurations"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Put a Dirac mass of size w_j ≥ 0 at each location x_j in a finite family. The mass bound includes both endpoints. The integral becomes the sum of w_j K(x_j), and repeated locations contribute with their full weights."))),
                DescribeRole.Theorem))));
}
