using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class BinaryWordGeometryDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual binary-word tree geometry",
        H("Words, unit edits and bounded shortest paths"),
        Blocks(
            Paragraph(Text("A word is a finite list of Boolean letters in its physical order. APPEND adds one letter at the right end; POP removes exactly that last letter. A path is an actual finite sequence of these edits. Its length counts every edit, and Within requires the initial, intermediate and terminal words all to satisfy the given height bound.")),
            Definition("Word", "Actual binary words", "Word is the type List Bool, including the empty word and every finite physical bit sequence."),
            Definition("lcp", "Longest common initial word", "The function compares the first letters, retains equal letters and stops at the first difference or at an empty word."),
            Definition("Step", "Actual unit operations", "The two constructors relate w to w followed by one Boolean letter, and that extended word back to w. No other transition has unit cost."),
            Definition("Path", "Actual edit sequences", "An empty sequence stays at its word. A nonempty sequence consists of one actual Step followed by another actual sequence with the matching endpoint."),
            Definition("length", "Charged path length", "The empty sequence has length zero; each actual edit adds one."),
            Definition("Within", "All intermediate heights", "For every path p and natural height L, Within(p,L) requires every word in the sequence, including both endpoints, to have length at most L."),
            Definition("distance", "Common-prefix distance", "For any words u and v, distance(u,v) is length(u)+length(v)-2*length(lcp(u,v)), using natural subtraction. The common prefix is no longer than either word."),
            Describe.Lean(DescribeId.Create("shortest-pop-append"),
                DeclarationHandle.Create(Owner + "shortest_pop_append"),
                H("Exact shortest actual POP/APPEND distance"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every two actual binary words u and v, lcp(u,v) is a prefix of each and contains every common prefix. Every actual edit path from u to v has length at least distance(u,v). There exists an actual path of exactly that length, all of whose word lengths are at most max(length(u),length(v)). The proof bounds the change in distance under each literal APPEND or POP, then constructs the attaining sequence by popping the suffix of u to the common prefix and appending the suffix of v. Empty words and coincident endpoints are included."))),
                DescribeRole.Theorem),
            Paragraph(Text("For the finite tree consisting of words of length at most L, endpoints in that tree therefore have a shortest path entirely inside the same tree. This supplies the operation-distance statement in section 39 of Recursive Relational Observation IV. The exact distinct unordered near-pair count IV.113, its finite representation bijection, recorder injection IV.112, bound IV.114 and closed form IV.115 are not established here.")))));

    private static DocumentBlock Definition(string selector, string title, string prose) =>
        Describe.Lean(DescribeId.Create(selector.Replace('.', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Owner + selector), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
