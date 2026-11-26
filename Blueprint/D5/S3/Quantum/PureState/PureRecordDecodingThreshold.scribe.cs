using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class PureRecordDecodingThresholdDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The scalar success curve has logarithmic slope minus one quarter at zero.",
        H("Finite-scale limit of the scalar decoding law"),
        Blocks(
            Describe.Lean(DescribeId.Create("scalar-crossover"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/PureState/PureRecordDecodingThreshold.joint_success_crossover"),
                H("The success powers converge to exp(−scale / 4)"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let x_n be real and k_n be a natural copy count. Assume x_n tends to zero, is eventually nonzero, and k_n x_n tends to the finite real scale. Then ((1 + sqrt(1 - x_n)) / 2)^k_n tends to exp(−scale / 4). For the decoding application x_n is the squared overlap, while the scalar theorem allows real inputs.")),
                    Paragraph(Text("The logarithm of the one-label success curve has derivative −1/4 at zero. The slope limit on the punctured neighborhood combines with the copy scale, and exponentiation gives the claimed limit."))),
                DescribeRole.Theorem))));
}
