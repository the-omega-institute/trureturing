using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class FerrersLevelCountingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/FerrersLevelCounting.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/barrese2023levels");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The local Gaussian coefficients combine through a finite state consisting of the previous last-row length.",
        H("Finite Ordered Level Recurrence"),
        Blocks(
            Node("ferrerslevelcounting-paths", "Compatible levels", "Paths",
                "For a bottom-to-top list a, Paths(r,U,a,u) is the set of all consecutive prescribed levels beginning below the row bound u. A nonempty path chooses its first last-row length v in {0,...,U}, a level of total a_1 with bound u and last row v, and the remaining path with bound v. The empty list has one empty path.", DescribeRole.Definition),
            Node("ferrerslevelcounting-count", "Evaluated finite recurrence", "count",
                "Define F([],u)=1 and F(a::as,u)=sum over v=0,...,U of T_a(u,v)F(as,v). The total starting value is F(a,U). Every summation runs over the U+1 possible row bounds, rather than over boards. Together with q-Pascal for the Gaussian polynomial, this is an explicit finite evaluation on the original data.", DescribeRole.Definition),
            Node("ferrerslevelcounting-paths-card", "Cardinality of compatible levels", "paths_card",
                "For every r,U,a,u, the number of compatible paths equals F(a,u). The proof splits a nonempty path into its unique first state, first level and remainder; finite dependent-sum and product cardinalities give the recurrence, and level_card supplies each entry.", DescribeRole.Theorem),
            Node("ferrerslevelcounting-rowindex", "Absolute row position", "rowIndex",
                "For a level size m, t levels, a level index p and a within-level index j, rowIndex is the ambient index mp+j in the mt-row tuple. The finite-index bound is part of the definition, so zero dimensions introduce no artificial row.", DescribeRole.Definition),
            Node("ferrerslevelcounting-flatfiber", "Flat row fiber", "FlatFiber",
                "A flat fiber consists of a weakly decreasing tuple of (r+1) times length(a) row lengths in {0,...,U}, bounded by u, with each consecutive block of r+1 rows summing to the corresponding ordered entry of a. No permutation of a is taken.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
