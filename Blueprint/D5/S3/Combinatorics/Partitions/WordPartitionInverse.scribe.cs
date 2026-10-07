using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class WordPartitionInverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/WordPartitionInverse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Decreasing padded prefix rows, with their endpoint bound, reconstruct one ordered binary word. The full fixed-count, fixed-area joint image is finite and agrees with the image of these actual partitions and of nonempty native trees.",
        H("Word reconstruction and the full joint image"),
        Blocks(
            Node("rows-word", "The guarded inverse word", "wordOfRows_spec", DescribeRole.Theorem,
                "Given a decreasing list of natural row lengths bounded by u, build the word by constructing the remaining rows at the first row's endpoint, appending a false letter, then adding the remaining true letters. The resulting word has exactly u true letters and one false letter per row, and its reverse prefix list is exactly the given list. Zero rows and the empty list remain valid."),
            Node("word-rows-word", "Recovering the same word", "wordOfRows_inverse", DescribeRole.Theorem,
                "Applying the construction to the actual reverse prefix rows and true count of any word recovers that very word, including the empty auxiliary word and pure-letter words. This recovers the ordered word; it does not recover forgotten tree brackets."),
            Node("zero-padding-word", "Padding rows by zeros", "wordOfRows_padding", DescribeRole.Theorem,
                "Appending zero rows corresponds exactly to prepending that many false letters to the reconstructed word. Zero padding does not replace the core word or normalize its area."),
            Node("zero-padding-cells", "Padding preserves the same cells", "padding_diagram", DescribeRole.Theorem,
                "Appending zero rows to a decreasing list leaves its Young diagram unchanged. Thus the padded row carrier retains its declared length while the actual cells and transpose remain the same."),
            Node("outer-reversal", "Exact complete-word reversal", "outer_reverse_contract", DescribeRole.Theorem,
                "Reversing the complete word preserves both counts, complements its scattered pair count within the endpoint rectangle, and preserves both moment coordinates. This is a mathematical comparison of whole words; it grants no reversal operation on an unknown source."),
            Node("finite-image", "The full nonempty actual joint image", "finite_joint_partition_image", DescribeRole.Theorem,
                "For arbitrary integer endpoint and pair-count parameters, take every nonempty binary word with those exact counts. Their distinct joint moment outputs form a finite set, since each word has the fixed length u plus v. This set equals the image of bounded decreasing padded rows at the direct pair count and also equals the moment image of native nonempty ordered binary trees. Complete-word reversal identifies this same joint image with the complementary pair count, and its capacity equals the native image cardinality. Negative counts, invalid pair counts and the empty endpoint produce no word source. Each nonempty word has the displayed left-comb representative; recovering an actual tree requires an additional left-comb promise. A representative supplies no physical acquisition, source-membership certification, mutation, calibration or other source authority. No sparse capacity bound or thick-frame family inverse is asserted here.")),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        DescribeRole role, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
