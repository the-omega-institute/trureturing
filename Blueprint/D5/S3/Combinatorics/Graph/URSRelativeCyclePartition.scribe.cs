using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class URSRelativeCyclePartitionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/URSRelativeCyclePartition.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/iurlano2026pairwise");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual reflected incidences restrict every invariant partition of the moved support of two relative rows. All fibres and joint counts use one indexed array.",
        H("Invariant partitions of relative moved support"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("relative"),
                DeclarationHandle.Create(Prefix + "relative"),
                H("Relative row coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The relative permutation of row t with respect to row r is rho(r) inverse composed with rho(t). It acts on the original column set and retains all actual row indices."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("moved-support"),
                DeclarationHandle.Create(Prefix + "movedSupport"),
                H("Moved support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The moved support D contains exactly those original columns not fixed by the relative permutation of rows r and s."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-invariant-moved-support-bound"),
                DeclarationHandle.Create(Prefix + "actual_invariant_moved_support_bound"),
                H("The invariant partition bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Let n be odd and at least three. An indexed family of 2n permutations on Fin n has actual column-symbol fibres of size two, and equal joint counts for reflected patterns whenever their columns and symbols are distinct. Choose distinct row indices r,s and let sigma be rho(r) inverse composed with rho(s). For any subset U of its moved support D with sigma(U)=U, put V=D minus U. Then n+|D| is at most |U| squared plus |V| squared plus one. Either block may be empty; commutation, sorting, identity-first and distinct-permutation assumptions are unnecessary.")),
                    Paragraph(Text("Saturation makes the entries of every third row that remain in the agreement set form fixed-point-free transpositions. Its actual D-to-D count is consequently odd. Original reflected incidences also force each two-step segment through the agreement set to return to its source or to its sigma-image. Contracting these segments gives a genuine permutation of D whose crossing edges between U and V are all uncontracted and occur equally in both directions. Each third row therefore has an odd positive actual within-block count.")),
                    Paragraph(Text("The actual fibre frequencies give total within-block count 2(|U| squared plus |V| squared). Rows r and s contribute |D| each, while the remaining 2n-2 rows contribute at least one each. Double counting proves the bound. This restriction alone does not settle bipartiteness of the fibre graph."))),
                DescribeRole.Theorem)),
        []));
}
