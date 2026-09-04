using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

// Source-bound projection for the M19.1 finite block-sample transport.
internal sealed class PublishedGoldenBase4BlockSample79Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first 79 exact golden-ratio base-four power records are transported losslessly into binary Zeckendorf first-return coordinates.",
        H("Published Golden Base-Four Block Sample 79"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("published-base4-block-sample-79-expands"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/PublishedGoldenBase4BlockSample79.publishedBlockSample79_expand"),
                H("Every block record expands to its canonical power word"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finite decoder is checked on all indices zero through seventy-eight. The totalized fallback is therefore unreachable on the declared sample.")),
                    Paragraph(Text(
                        "Expansion recovers the unique arithmetic word supplied by the existing golden base-four oracle, so no second dictionary or Zeckendorf implementation is introduced."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("published-base4-machine-skeleton-sample-equivalence"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/PublishedGoldenBase4BlockSample79.machineFitsPowerSample79_iff_extractSkeletonFits"),
                H("Machine fitting is equivalent to recurrent-skeleton fitting"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "M17 extraction commutes pointwise with the first-return coordinate change. Hence a typed partial DFAO fits the original 79 power words exactly when its extracted recurrent skeleton fits the transported block sample.")),
                    Paragraph(Text(
                        "The distinguished zero-input anchor remains separate and is carried by the anchored machine semantics used by the published experiment."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S0/Automata/BinaryZeckendorfBlockSkeleton")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S1/Digit/GoldenBase4AutomataOracle")),
        ]));
}
