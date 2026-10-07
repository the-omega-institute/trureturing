using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PatternMatchings;

internal sealed class P13DecoderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PatternMatchings/P13Decoder.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/biswas2026matchingtriples");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered endpoint queues decode every permitted rank into an actual perfect matching.",
        H("Constructing a matching from every accepted scan"),
        Blocks(
            Node("p13-p13decoder-decodepairs", "The general-rank queue algorithm", "decodePairs",
                "Opening appends the current vertex. Closing pairs it with the selected queue entry and deletes that entry. The algorithm tests only the selected rank and final empty queue, without inspecting a source pattern.", DescribeRole.Definition),
            Node("p13-p13decoder-decode-pairs", "Exact endpoint coverage", "decode_pairs",
                "For equal-length vertex and action lists and a valid initial base whose old-plus-pending size equals the queue length, every accepted suffix decodes. Its concatenated pair endpoints are a permutation of the queue followed by the full unscanned vertex list.", DescribeRole.Theorem),
            Node("p13-p13decoder-realizes", "Realization by a partner map", "Realizes",
                "A realization follows the entire scan: an opening has a later partner, and a closing vertex has the selected queue entry as its actual partner. It assumes no avoidance law.", DescribeRole.Definition),
            Node("p13-p13decoder-encodefrom", "Recording the actual active rank", "encodeFrom",
                "The deterministic encoder records openings and, at a closure, the index of the actual partner in the opener queue.", DescribeRole.Definition),
            Node("p13-p13decoder-decoded-realizes", "Decoded pairs realize the complete scan", "decoded_realizes",
                "With increasing queue and vertex lists, all queued vertices earlier than the remaining vertices, and a partner map realizing every decoded pair, the complete ranked scan is realized by that partner map.", DescribeRole.Theorem),
            Node("p13-p13decoder-realizes-encode", "Recovery of all recorded ranks", "realizes_encode",
                "Encoding any realization with the natural endpoint order recovers exactly the same ranked scan. The increasing queue has no duplicate opener, so its selected index is recovered uniquely.", DescribeRole.Theorem),
            Node("p13-p13decoder-decodematching", "The decoded actual perfect matching", "decodeMatching",
                "For a complete accepted scan, decode all vertices of Fin(2n) in increasing order. Exact endpoint coverage gives a list with no duplicate endpoint. Its partner map is an involution with no fixed point, using the generic disjoint-pair involution theorem.", DescribeRole.Definition),
            Node("p13-p13decoder-decode-realizes", "The constructed matching realizes its scan", "decode_realizes",
                "The perfect matching decoded from any accepted scan realizes every action and selected opener of that full scan.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
