using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs;

internal sealed class HardinA233200LiteralBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200LiteralBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact weighted fibres of the eight-colour row-major scanner.",
        H("Individual colours and complementary-pair labels"),
        Blocks(
            Paragraph(Text("The four pair labels have colour fibres {0,7}, {1,6}, {2,5}, and {3,4}. "
                + "The three scanner flags record actual earlier occurrences of colours one, two, and three. "
                + "A pair label retains both the allowed-colour multiplicity and the resulting flags.")),
            Node("labelAdvance", "Pair-label scanner transition",
                "An allowed colour in pair one sets the first flag; an allowed colour in pair two "
                + "sets the second, and pair three sets the third. A forbidden colour contributes zero weight.", DescribeRole.Definition),
            Node("labelWeight", "Multiplicity of one pair label",
                "Pair zero always has two lifts. Pair one has one lift before colour one appears "
                + "and two afterwards. Pair two has no lift before colour one, one lift before "
                + "colour two, and two lifts afterwards. Pair three has no lift before colours one and two, one lift before colour three, and two afterwards.", DescribeRole.Definition),
            Node("rowFinish", "Scanning the entire pair row",
                "Every cell is scanned in order, with no discarded scanner information.",
                DescribeRole.Definition),
            Node("rowWeight", "The exact row multiplicity",
                "Multiply the successive single-cell weights using the evolving scanner flags.",
                DescribeRole.Definition),
            Node("scanner_fibres", "The exact weighted scanner sum",
                "For every word length, initial scanner state, and integer readout of final flags "
                + "and the entire pair word, summing over allowed individual colour words equals "
                + "the pair-word sum with these weights. Splitting off the first cell gives the "
                + "induction; the eight single-cell cases supply the exact fibres. This identity "
                + "does not assume that every distinguished colour occurs. The source.params audit binding is unfinished under https://github.com/the-omega-institute/trureturing/issues/28653.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
