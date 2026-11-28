using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class P48qCubicTwiningCharacterDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/P48qCubicTwiningCharacter.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized trace series of the standard cubic lift on P48q",
        H("The P48q Cubic Twining Character"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("p48q-cubic-twining-trace-term"),
                DeclarationHandle.Create(Prefix + "traceTerm"),
                H("Normalized full-grade trace term"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At each integer grade n, the actual standard cubic lift acts on the full Sugawara eigenspace. Its trace is multiplied by exp(2 pi i tau (n - 48/24))."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("p48q-cubic-twining-character"),
                DeclarationHandle.Create(Prefix + "actualCubicTwiningCharacter"),
                H("Actual cubic twining character"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The character is the sum of the normalized full-grade trace terms over all integer grades."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("p48q-cubic-twining-fixed-charge-theta"),
                DeclarationHandle.Create(Prefix + "fixedChargeTheta"),
                H("Fixed-charge theta series"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The theta series sums exp(2 pi i tau E(a)) over the integral charges fixed by the cubic isometry, with E(a) equal to half of the original Gram square."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("p48q-cubic-twining-theta-div-eta"),
                DeclarationHandle.Create(Prefix + "actual_cubic_twining_character_eq_theta_div_eta"),
                H("Absolute convergence and the theta-eta formula"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For complex tau with positive imaginary part, the actual cubic twining trace terms are absolutely summable. Their sum equals the fixed-charge theta series divided by eta(3 tau) to the sixteenth power.")),
                    Paragraph(Text("The Gaussian bound for the positive P48q Gram controls the fixed-charge terms. The sixteen-colour occupation weights are absolutely summable at exp(2 pi i (3 tau)). The joint family groups by E(a) plus three times the occupation energy. Each fibre is the finite charge cutoff and occupation equation in the full-grade trace formula. Factoring the joint sum and evaluating the unsigned occupation series gives the eta factor, with 3 times 16/24 equal to the vacuum shift 48/24."))),
                DescribeRole.Theorem))));
}
