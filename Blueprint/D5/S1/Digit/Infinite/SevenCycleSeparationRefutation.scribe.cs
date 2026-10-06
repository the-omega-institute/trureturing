using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class SevenCycleSeparationRefutationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unconditional future separation.", H("Unconditional future separation"),
        Blocks(Describe.Lean(
            DescribeId.Create("sevencycleseparationrefutation-claim"),
            DeclarationHandle.Create("D5/S1/Digit/Infinite/SevenCycleSeparationRefutation.claim"),
            H("Universal finite separation assertion"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The assertion quantifies over every positive subcritical budget, original "
                + "endpoint graph and actual odd primitive singleton rival. It asks for one "
                + "finite horizon removing all different-first-label entries compatible with "
                + "that rival. The two first colors can differ; future common colors are tested "
                + "recursively using the original guards and full branch images."))),
            DescribeRole.Definition))));
}
