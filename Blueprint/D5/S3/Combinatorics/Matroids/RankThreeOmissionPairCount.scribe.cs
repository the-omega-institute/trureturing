using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class RankThreeOmissionPairCountDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/RankThreeOmissionPairCount";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For finite triple families with at most one triple per pair, the sizes of the ternary potential fibers determine how many pairs require coverage.",
        H("The Minimum Number of Rank-Three Omissions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rank-three-omissions-pair-count"),
                DeclarationHandle.Create(Module + ".potential_fiber_pair_count_le"),
                H("The mixed-pair lower bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let the normalized ternary potential space of a pair-unique family have dimension d. "
                    + "For any evaluation basis, write q for three to the power d and s for the size of its zero fiber. "
                    + "There are q times (q minus one) ordered pairs of distinct fiber labels, with s squared point pairs per label pair. "
                    + "Every such pair lies in a listed triple, and each triple offers six ordered pairs of positions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rank-three-omissions-lifted-line-attainment"),
                DeclarationHandle.Create(Module + ".exists_lifted_omission_family"),
                H("Lifted affine lines attain the bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive s, take the product of the d-dimensional ternary coordinate space and the cyclic group of order s. "
                    + "List triples with distinct first coordinates and zero sum in the product. Each mixed pair "
                    + "determines its unique third point by the negative-sum rule. Same-fiber pairs force the normalized potentials "
                    + "to be constant on rows. The coordinate functions are independent potentials, while surjectivity of basis evaluation "
                    + "on the row labels bounds the potential dimension by d. All six ordered pairs of each listed triple are mixed, "
                    + "so the family meets the lower bound with equality."))),
                DescribeRole.Theorem))));
}
