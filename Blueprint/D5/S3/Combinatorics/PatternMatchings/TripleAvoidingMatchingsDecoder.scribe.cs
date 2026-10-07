using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PatternMatchings;

internal sealed class TripleAvoidingMatchingsDecoderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDecoder.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/biswas2026matchingtriples");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An ordered queue turns accepted action words into pairs covering every vertex exactly once.",
        H("Decoding accepted action words into perfect matchings"),
        Blocks(
            Node("bss-decoder-acceptfrom", "Acceptance at a given height and phase", "AcceptFrom",
                "A state consists of a nonnegative height h and a phase indicating whether an oldest closure is required. An opening increases h and preserves the phase. An oldest closure requires positive height, decreases h by one and clears the phase. A second closure requires the normal phase and height at least two; it decreases h by one and sets the required phase exactly when the preceding height was at least three. The empty suffix is accepted exactly at height zero in the normal phase.", DescribeRole.Definition),
            Node("bss-decoder-accepted", "Accepted words of prescribed length", "Accepted",
                "For a nonnegative integer n, Accepted(n) consists of action words of length 2n accepted from height zero in the normal phase. The two closing letters remain distinct.", DescribeRole.Definition),
            Node("bss-decoder-decodepairs", "Pairing vertices with an ordered queue", "decodePairs",
                "An opening appends the current vertex to the queue. An oldest closure pairs the current vertex with the first queued vertex and removes that vertex. A second closure pairs it with the second queued vertex, retaining the first. Decoding succeeds at the end exactly when the queue and the remaining vertex and action lists are empty; incompatible lists give no pairing.", DescribeRole.Definition),
            Node("bss-decoder-decode-pairs", "Every accepted word yields all endpoint pairs", "decode_pairs",
                "Let q be an initial queue and let vs be an unscanned vertex list of the same length as an action word w. If w is accepted from height equal to the length of q in either phase, decoding produces a pair list whose concatenated endpoints are a permutation of q followed by vs.", DescribeRole.Theorem),
            Node("bss-decoder-pairfunction", "The partner map of a pair list", "pairFunction",
                "For a list of pairs, the partner map exchanges the two endpoints of the first pair containing the argument. Vertices absent from every pair are fixed.", DescribeRole.Definition),
            Node("bss-decoder-pairfunction-spec", "Disjoint endpoint pairs give an involution", "pairFunction_spec",
                "If the concatenated endpoints of a pair list have no repetitions, its partner map is an involution. A vertex is fixed exactly when it does not occur among those endpoints.", DescribeRole.Theorem),
            Node("bss-decoder-decodematching", "The matching decoded from an accepted word", "decodeMatching",
                "Decode an accepted word of length 2n using the empty initial queue and the vertices in increasing order. The resulting endpoint pairs cover each vertex exactly once, and their partner map defines a perfect matching.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
