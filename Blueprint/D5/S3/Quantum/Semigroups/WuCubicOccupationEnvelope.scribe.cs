using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuCubicOccupationEnvelopeDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuCubicOccupationEnvelope.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An occupation bound for the directed cubic spectral sum.",
        H("Cubic occupation envelope"),
        Blocks(
            Describe.Lean(DescribeId.Create("cubic-deficit-gt"),
                DeclarationHandle.Create(Owner + "cubic_deficit_gt"),
                H("Strict lower bound under the CAR constraints"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Wu),
                Blocks(
                    Paragraph(Text("Fix the ascending spectrum λ = (262144, 531441, 551368, 1030301)/2375254 " +
                        "and h = 3 log(9/8). Let w be nonnegative directed weights with " +
                        "∑ⱼ(wᵢⱼ + wⱼᵢ) = 2 and wᵢⱼ + wⱼᵢ ≤ 1 for i < j. Let eᵢ ∈ [0,1] satisfy " +
                        "∑ᵢ eᵢ = 2 and wᵢᵢ = eᵢ(1 − eᵢ). The directed moment " +
                        "∑ᵢ<ⱼ(wᵢⱼ − wⱼᵢ)(λⱼ − λᵢ) is 2m, where |m| ≤ ∑ᵢ eᵢ|λᵢ − v| for every real v.")),
                    Paragraph(Text("Write xᵢ = λᵢ^(1/3). The directed energy is E₃(w) = " +
                        "(9/(8 cosh h)) ∑ᵢⱼ wᵢⱼ [exp(h)λᵢ + exp(−h)λⱼ − " +
                        "exp(h/3)xᵢ²xⱼ − exp(−h/3)xᵢxⱼ²]. " +
                        "With α₃ = (9/2) sinh(h/3) sinh(2h/3)/(2h sinh h) and " +
                        "H(m) = ∑ᵢ λᵢ log(4λᵢ) + 2 log(cosh h) − 2hm, " +
                        "the normalized deficit (4 cosh(h)/9)(E₃(w) − α₃ H(m)) exceeds 1/8000.")),
                    Paragraph(Text("The cubic expansion yields a symmetric edge cost, a linear term in m, " +
                        "and a nonnegative reverse-edge contribution. The symmetric cost separates into a reference cost, " +
                        "nonnegative edge corrections and a weighted sum of (eᵢ − 1/2)². " +
                        "Centering the spectral distances in the moment bound and applying weighted Cauchy–Schwarz " +
                        "bounds this sum from below. Completing the square and enclosing the logarithms by rational " +
                        "bounds gives the stated margin."))),
                DescribeRole.Theorem))));
}
