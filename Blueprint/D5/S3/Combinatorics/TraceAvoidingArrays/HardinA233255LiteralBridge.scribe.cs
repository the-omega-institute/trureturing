using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233255LiteralBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact weighted fibres of the six-colour row-major scanner.",
        H("Individual colours and complementary-pair labels"),
        Blocks(
            Paragraph(Text("The three pair labels have colour fibres {0,5}, {1,4}, and {2,3}. "
                + "The two scanner flags record actual earlier occurrences of colours one and two. "
                + "A pair label retains both the allowed-colour multiplicity and the resulting flags.")),
            Node("labelAdvance", "Pair-label scanner transition",
                "An allowed colour in pair one sets the first flag; an allowed colour in pair two "
                + "sets the second flag. A forbidden colour contributes zero weight.", DescribeRole.Definition),
            Node("labelWeight", "Multiplicity of one pair label",
                "Pair zero always has two lifts. Pair one has one lift before colour one appears "
                + "and two afterwards. Pair two has no lift before colour one, one lift before "
                + "colour two, and two lifts afterwards.", DescribeRole.Definition),
            Node("rowFinish", "Scanning the entire pair row",
                "Every cell is scanned, including the first cell that is absent from the next boundary.",
                DescribeRole.Definition),
            Node("rowWeight", "The exact row multiplicity",
                "Multiply the successive single-cell weights using the evolving scanner flags.",
                DescribeRole.Definition),
            Node("scanner_fibres", "The exact weighted scanner sum",
                "For every word length, initial scanner state, and integer readout of final flags "
                + "and the entire pair word, summing over allowed individual colour words equals "
                + "the pair-word sum with these weights. Splitting off the first cell gives the "
                + "induction; the six single-cell cases supply the exact fibres. This identity "
                + "does not assume that either distinguished colour occurs.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
