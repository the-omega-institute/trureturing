using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.WernerHolevo;

internal sealed class Chirped69ActualSeedBoundsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped69ActualSeedBounds";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact order-69 correlation system has a unique zero in its certificate ball.",
        H("Root certification in order 69"),
        Blocks(
            Describe.Lean(DescribeId.Create("exists-unique-zero-closed-ball"),
                DeclarationHandle.Create(Module + ".existsUnique_zero_closedBall"),
                H("Unique zero in the order-69 certificate ball"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The 63 real Cayley coordinates determine the four seed layouts. Exact integer replay "
                    + "checks the seed values, slopes, residual and preconditioned derivative defect at "
                    + "the dyadic center. The analytic derivative agrees with the replay Jacobian and has "
                    + "operator norm drift bounded by 16 times the distance. These estimates certify a "
                    + "unique zero on the closed sup-norm ball of radius 2⁻³⁰."))),
                DescribeRole.Theorem))));
}
