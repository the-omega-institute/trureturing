using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaLinear;

internal sealed class OfflineZeroCharacterDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Weil/ZetaLinear/OfflineZeroCharacter.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Offline-zero parameters define continuous log-scale Mellin characters, with real "
            + "part measuring the obstruction to unitarity.",
        H("Offline-Zero Nonunitary Characters"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("offline-zero-log-scale-character"),
                DeclarationHandle.Create(DeclarationPrefix + "offlineZeroCharacter"),
                H("The log-scale character of an offline zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a complex zero parameter rho, the definition realizes the "
                            + "continuous character t maps to exp((rho - 1/2)t) from the "
                            + "additive real line, represented multiplicatively, to the "
                            + "complex numbers.")),
                    Paragraph(Text(
                        "The accompanying Lean theorems split this value as exp(delta t) "
                            + "times exp(i gamma t), identify unitarity with delta equal to "
                            + "zero, and prove the parameter sequence from the imaginary "
                            + "axis through the complex plane to the real-part obstruction "
                            + "is short exact.")),
                    Paragraph(Text(
                        "The definition is not empty or vacuous: "
                            + "exists_nonunitary_offline_zero_character constructs rho equal "
                            + "to one and proves that its character is genuinely nonunitary."))),
                DescribeRole.Definition))));
}
