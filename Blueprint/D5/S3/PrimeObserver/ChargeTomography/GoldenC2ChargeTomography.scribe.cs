using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeObserver.ChargeTomography;

internal sealed class GoldenC2ChargeTomographyDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/PrimeObserver/ChargeTomography/GoldenC2ChargeTomography.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Neutral and quadratic charge channels invert split and inert populations.",
        H("Golden C2 Charge Tomography"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-c2-analysis-is-bijective"),
                DeclarationHandle.Create(Prefix + "analyze_charge_bijective"),
                H("Neutral-plus-charge analysis is bijective"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The analysis map records the sum and difference of the split and inert "
                            + "coordinates.")),
                    Paragraph(Text(
                        "The synthesis map divides the sum and difference of those channels by "
                            + "two, giving two-sided inverse identities.")),
                    Paragraph(Text(
                        "This is finite C2 tomography. Arithmetic interpretation is supplied by "
                            + "the separate golden prime classification owner."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("neutral-channel-loses-charge"),
                DeclarationHandle.Create(Prefix + "neutral_channel_not_injective"),
                H("The neutral channel alone is not faithful"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A unit split population and a unit inert population have equal neutral "
                            + "totals while remaining distinct states."))),
                DescribeRole.Theorem))));
}
