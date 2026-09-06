using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.PartialIdentification;

internal sealed class ReducedResponseTableMomentsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/PartialIdentification/ReducedResponseTableMoments.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fourth row probability is determined by the first three and normalization. Exact rational compression preserves the retained expectations on the original response-table carrier.",
        H("Three-cell response-table compression"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-law-support"),
                DeclarationHandle.Create(Prefix + "finiteLawSupport"),
                H("Actual nonzero support"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Counts nonzero masses on the original finite carrier, rather than only the size of a latent presentation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sparse-support-card"),
                DeclarationHandle.Create(Prefix + "momentCompression_sparse_support_card_le"),
                H("Pushforward cannot enlarge support"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every nonzero sparse mass is in the image of a retained latent profile. Its support size is bounded by the profile count."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-coordinate"),
                DeclarationHandle.Create(Prefix + "momentCompression_sparse_coordinate_eq"),
                H("Original-carrier feature preservation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Combines the existing coordinate identity with the existing original-carrier pushforward theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reduced-table-feature"),
                DeclarationHandle.Create(Prefix + "reducedTableFeature"),
                H("Three indicators per row"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reuses the established quaternary response encoding and retains digits zero, one and two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("three-cell-reconstruction"),
                DeclarationHandle.Create(Prefix + "boolean_pair_law_eq_of_first_three"),
                H("Recover the omitted fourth cell"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Equality of three cells between two normalized response laws forces equality of the fourth cell."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("moment-is-row-cell"),
                DeclarationHandle.Create(Prefix + "reducedTableFeature_moment_eq_cell"),
                H("Bind moments to actual row distributions"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The feature expectation is exactly a cell of the existing tableEvaluationLaw pushforward."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reduced-moments-preserve-rows"),
                DeclarationHandle.Create(Prefix + "reducedTableMoments_preserve_rows"),
                H("Preserve all complete row laws"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The three retained expectations in each row determine its full four-cell law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("three-cell-table-compression"),
                DeclarationHandle.Create(Prefix + "exists_three_cell_table_compression"),
                H("At most 3k+1 atoms for all row laws"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Constructs a rational replacement law with every row marginal unchanged. Cross-row dependence is allowed to change."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("three-cell-query-compression"),
                DeclarationHandle.Create(Prefix + "exists_three_cell_query_compression"),
                H("At most 3k+2 atoms with an additional query"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Preserves all complete row marginals and one arbitrary rational table-query expectation on the same original table carrier."))),
                DescribeRole.Theorem))));
}
