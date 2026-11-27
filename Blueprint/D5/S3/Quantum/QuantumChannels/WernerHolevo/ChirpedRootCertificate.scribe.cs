using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.WernerHolevo;

internal sealed class ChirpedRootCertificateDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedRootCertificate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A preconditioned certificate for a unique zero.",
        H("A preconditioned certificate for a unique zero"),
        Blocks(
            Describe.Lean(DescribeId.Create("exists-unique-zero-closed-ball"),
                DeclarationHandle.Create(Module + ".existsUnique_zero_closedBall"),
                H("A unique root in the certified ball"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a closed ball in a complete finite-dimensional real normed space, bound the defect of the "
                    + "preconditioned derivative at the center and bound derivative drift on the whole ball. Their sum "
                    + "with the stated radius and preconditioner factor bounds the contraction constant. The "
                    + "additional center displacement bound ensures that the update maps the ball into itself. "
                    + "Injectivity of the preconditioner follows from the defect bound and finite dimensionality."))),
                DescribeRole.Theorem))));
}
