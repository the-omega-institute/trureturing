using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeObserver.ChargeTomography;

internal sealed class SharedChargeDifferentShellsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/PrimeObserver/ChargeTomography/SharedChargeDifferentShells.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Observer shells may share one charge quotient while retaining different kernels.",
        H("Shared Charge, Different Shells"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("shell-equality-implies-charge-equality"),
                DeclarationHandle.Create(
                    Prefix + "shell_equality_implies_charge_equality"),
                H("Every charge-reading shell refines charge equality"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A charge decoder factors the common charge through a shell readout.")),
                    Paragraph(Text(
                        "Consequently, any state pair identified by the shell must also have "
                            + "equal decoded charge.")),
                    Paragraph(Text(
                        "The converse is not assumed because a shell may retain extra hidden "
                            + "coordinates above the common charge quotient."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("shared-charge-does-not-identify-observers"),
                DeclarationHandle.Create(
                    Prefix + "fine_and_charge_shells_have_different_faithfulness"),
                H("Shared charge does not force observer identity"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The identity shell on a Boolean pair is injective, while its first "
                            + "coordinate charge shell is not.")),
                    Paragraph(Text(
                        "Both admit the same first-coordinate charge decoder, providing an "
                            + "explicit different-kernel witness."))),
                DescribeRole.Theorem))));
}
