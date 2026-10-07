using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class SevenCycleSeparationRefutationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unconditional future separation.", H("Unconditional future separation"),
        Blocks(Paragraph(Text("The two actual sources repeat the seven windows 3,3,5,5,3,2,2 and 0,3,5,5,3,2,2. Strict actual entry records against the same rival have a shared literal tail, fixed common future errors and a positive uniform margin. That tail belongs to every recursively defined finite horizon.")), Describe.Lean(
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
