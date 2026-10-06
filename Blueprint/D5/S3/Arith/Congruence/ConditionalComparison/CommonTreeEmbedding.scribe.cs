using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence.ConditionalComparison;

internal sealed class CommonTreeEmbeddingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ranking the chosen children of one finite tree gives compatible injections at every depth, exactly the selected leaves at full depth, and the native prefix-union event identity.",
        H("A Common Embedding for All Prefix Events"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("common-tree-ranked-embedding"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/ConditionalComparison/CommonTreeEmbedding.rank_encode_coherent_and_exact"),
                H("Natural child ranks give one coherent and exact path encoding"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix integers 2 <= r < s, any finite height B >= 0, "
                        + "and one native tree Theta. At positive height its "
                        + "root contains an r-element subset S of the target "
                        + "alphabet {0,...,s-1} and a subtree for every target "
                        + "digit, including unvisited digits. The construction "
                        + "is pointwise in this full tree and requires no "
                        + "probability law or target query word.")),
                    Paragraph(Text(
                        "For any depth j <= B and source word x of length j "
                        + "over {0,...,r-1}, rankEncode returns the empty word "
                        + "when j = 0. At positive depth, the source head "
                        + "selects its naturally ordered rank in S, producing "
                        + "a target digit a. The output is a followed by the "
                        + "encoding of the source tail in the actual subtree "
                        + "Theta_a. Every depth and every event use this "
                        + "same computation on Theta.")),
                    Paragraph(Text(
                        "The theorem has four conclusions. First, the map "
                        + "at every depth j <= B is injective. Second, an "
                        + "arbitrary target word w of length B is selected "
                        + "by the native recursive selection predicate if "
                        + "and only if it equals rankEncode of some source "
                        + "word of length B. Selection is defined independently "
                        + "of the encoder, so this identifies its entire "
                        + "full-depth image.")),
                    Paragraph(Text(
                        "Third, for every j <= k <= B and every length-k "
                        + "source word x, encoding its first j digits equals "
                        + "taking the first j digits of its length-k encoding. "
                        + "Both maps use the same Theta. Equal source heads "
                        + "produce the same target head and hence the same "
                        + "actual child subtree, where the shorter-height "
                        + "argument applies. For exactness, a selected target "
                        + "head is inverted by the natural order isomorphism "
                        + "onto S, and its entire selected tail is recovered "
                        + "recursively in that target child.")),
                    Paragraph(Text(
                        "Fourth, take any finite family P of native target "
                        + "prefixes, each with its own depth at most B. A "
                        + "prefix-hit means that some selected B-leaf extends "
                        + "that prefix. Let F_P contain every ambient B-word "
                        + "extending at least one member of P, without any "
                        + "selection restriction. At every Theta, some "
                        + "prefix-hit in P occurs if and only if Theta hits "
                        + "F_P. The same selected leaf witnesses both sides, "
                        + "which gives equality of these events on the native "
                        + "tree sample space.")),
                    Paragraph(Text(
                        "Height zero and empty words are included. P may "
                        + "be empty, contain the empty prefix, mix lengths, "
                        + "overlap, or contain full-depth words. No disjointness "
                        + "or prefix-free assumption is used. Since r is "
                        + "positive, every source prefix can be extended to "
                        + "length B by filling the remaining digits with zero. "
                        + "Exactness and truncation compatibility then give a "
                        + "selected leaf extending its encoded prefix. Thus "
                        + "reached nodes at depths strictly less than B have r "
                        + "selected successors, while the empty-prefix event "
                        + "is the whole sample space. All heights here "
                        + "are finite; no coupling across different heights "
                        + "or infinite-branch assertion is made."))),
                DescribeRole.Theorem))));
}
