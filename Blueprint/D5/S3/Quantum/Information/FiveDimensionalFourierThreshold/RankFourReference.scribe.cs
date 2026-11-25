using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.FiveDimensionalFourierThreshold;

internal sealed class RankFourReferenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/RankFourReference.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact rank-four extremal rays yield simultaneous bounds on the four complementary nonzero rows and the total mass on those rows.",
        H("Rank-four extremal ray estimates"),
        Blocks(
            Describe.Lean(DescribeId.Create("five-sharp-rank-four-reference"),
                DeclarationHandle.Create(Prefix + "RankFourReference"), H("Joint reference estimates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Write σ = √((5 + √5)/10) and b = √((3 − √5)/10). For a critical four-row mask, the difference of its Born masses on two unit states equals 1 + σ − dx − dy for nonnegative spectral deficits dx and dy. The phase-aligned distances rx and ry satisfy (σ − b)rx² ≤ 2dx and (1 − σ)ry² ≤ 2dy. The complementary tail has total first-state square-root mass at least √(1 − σ) − √2 rx. On each tail row, the first-state amplitude norm is at most √(1 − σ)/2 + rx and the second-state amplitude norm is at least √(2/(7 + √5)) − ry."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("five-sharp-rank-four-affine"),
                DeclarationHandle.Create(Prefix + "rankFourReference_affine"), H("The reference estimates for every affine critical four-row mask"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The centered mask selects the pair {2,3} in both bases and the tail consists of {1,4} in both bases. The top and kernel reference rays are obtained from the orthonormal eigenbasis. On each tail row their Born probabilities are respectively (1 − σ)/4 and 2/(7 + √5). The spectral gaps bound the errors after phase alignment, and the two-basis measurement operator bounds the total tail amplitude error by √2 times the state error. The affine state isometry carries these estimates to every transported mask by preserving the row amplitude norms."))), DescribeRole.Theorem)),
        []));
}
