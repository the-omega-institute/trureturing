using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Bridges;

internal sealed class InvolutionIntertwinerParityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Bridges/InvolutionIntertwinerParity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A typed bridge between involutions transports their parity sectors.",
        H("Involution Intertwiner Parity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("involution-fixed-sector-transport"),
                DeclarationHandle.Create(Prefix + "fixed_sector_maps"),
                H("Fixed sectors are transported"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The bridge commutes with the source and target involutions.")),
                    Paragraph(Text(
                        "Consequently, each source fixed point maps to a target fixed point."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("involution-odd-sector-transport"),
                DeclarationHandle.Create(Prefix + "odd_sector_maps"),
                H("Sign-changing sectors are transported"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an additive bridge, a source vector sent to its negative maps to a "
                            + "target vector with the same odd parity.")),
                    Paragraph(Text(
                        "A separate constant-bridge example shows why injectivity is needed to "
                            + "reflect parity information back to the source."))),
                DescribeRole.Theorem))));
}
