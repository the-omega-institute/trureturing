using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.PeriodicDaughterJointShortening;

internal sealed class WordsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ascending daughter blocks and the literal common-cut ear",
        H("Words for the periodic daughter construction"),
        Blocks(
            Paragraph(Text(
                "This helper module defines the physical labels and words used by the existing "
                    + "PeriodicDaughterJointShortening.Construction proof. The word identities "
                    + "organize the lower daughter blocks and shortened top block, while the "
                    + "permutation results provide the exact inventories consumed by "
                    + "daughter_order and the final periodic_daughter_joint_shortening theorem.")),
            Node("length_split", "The old length split",
                "For 2≤r, length d r=(r-1)*(d+1)+d, separating the complete lower blocks from the top old block.", DescribeRole.Theorem),
            Node("regularLabel", "Labels in a regular block",
                "regularLabel d r hr j i is the Fin (length d r) label j.val*(d+1)+i.val for a lower block j and daughter phase i.", DescribeRole.Definition),
            Node("topLabel", "Labels in the top block",
                "topLabel d r hr i is the Fin (length d r) label (r-1)*(d+1)+i.val for an old top digit.", DescribeRole.Definition),
            Node("daughterLabel", "Labels in a daughter block",
                "daughterLabel d r hr j i is the Fin (length d r+1) label j.val*(d+1)+i.val for daughter block j and phase i.", DescribeRole.Definition),
            Node("lowerWord", "The complete lower word",
                "lowerWord d r hr eta flatMaps eta through regularLabel over List.finRange (r-1). Construction uses it for all complete lower daughter blocks.", DescribeRole.Definition),
            Node("shortenedWord", "The shortened old word",
                "shortenedWord d r hr tau cut is lowerWord applied to earWord d tau cut, followed by tau mapped through topLabel. This is the old word constructed by Construction.", DescribeRole.Definition),
            Node("commonCut", "The physical common cut",
                "commonCut d r cut is (r-1)*(d+1)+cut, the cut after all complete lower blocks and inside the top word.", DescribeRole.Definition),
            Node("daughterWord", "The full periodic daughter word",
                "daughterWord d r hr eta flatMaps eta through daughterLabel over List.finRange r. Construction uses it as the target word after inserting the fresh label.", DescribeRole.Definition),
            Node("ear_prefix_sum", "The saturated ear-prefix sum",
                "For cut≤sigma.length and every h, the mapped sum of (earWord d sigma cut).take h equals the mapped sum of sigma.take (if h≤cut then h else h-1) on castSucc digits, plus the fresh final digit exactly when h>cut. Construction uses this prefix identity in top_block.", DescribeRole.Theorem),
            Node("ear_sum", "The complete ear sum",
                "The mapped sum of earWord d tau cut equals the mapped sum of tau castSucc digits plus the final fresh label. Construction uses this identity to compute the top block total.", DescribeRole.Theorem),
            Node("lower_length", "The lower word length",
                "If tau is a permutation of finRange d, the lower word built from earWord d tau cut has length (r-1)*(d+1).", DescribeRole.Theorem),
            Node("ear_after", "Ear transport across an append",
                "earWord k (xs++ys) (xs.length+cut) equals xs.map Fin.castSucc ++ earWord k ys cut. This locates the common cut across the lower/top append.", DescribeRole.Theorem),
            Node("literal_ear", "The literal global ear identity",
                "For a permutation tau of finRange d, taking the ear at commonCut from shortenedWord gives exactly daughterWord applied to earWord d tau cut. The final theorem uses this equality to identify the daughter ear literally.", DescribeRole.Theorem),
            Node("daughter_perm", "The daughter product inventory",
                "If eta permutes finRange (d+1), daughterWord d r hr eta permutes finRange (length d r+1). The proof enumerates the injective block-by-phase product, and Construction uses it for the daughter order.", DescribeRole.Theorem),
            Node("ear_perm", "The ear inventory",
                "If tau permutes finRange d, earWord d tau cut permutes finRange (d+1).", DescribeRole.Theorem),
            Node("removeFresh", "Removing the globally fresh label",
                "removeFresh k maps a Fin (k+1) label below k to the corresponding Fin k label and maps Fin.last k to none.", DescribeRole.Definition),
            Node("old_perm_of_ear", "Recovering the old inventory",
                "If earWord k sigma cut permutes finRange (k+1), filtering with removeFresh recovers sigma as a permutation of finRange k. Construction uses this deletion step for the shortened old word.", DescribeRole.Theorem),
            Node("shortened_perm", "The shortened old permutation",
                "If tau permutes finRange d, shortenedWord d r hr tau cut permutes finRange (length d r). This combines literal_ear, daughter_perm and ear_perm and is consumed by the final construction.")),
        []));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("periodic-daughter-words-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
