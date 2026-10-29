using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class FerrersLevelTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/FerrersLevelTransfer.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithSums/barrese2023levels");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A whole level is counted by a guarded Gaussian coefficient after its last row is fixed.",
        H("Gaussian Level Transitions"),
        Blocks(
            Node("ferrersleveltransfer-Level", "A prescribed level", "Level",
                "Level(r,U,u,v,a) consists of all weakly decreasing tuples of r+1 row lengths in {0,...,U}, each at most u, whose last row is v and whose sum is a. The actual level size is m=r+1.", DescribeRole.Definition),
            Node("ferrersleveltransfer-transition", "Explicit transition coefficient", "transition",
                "For 0 <= u,v <= U, the entry T_a(u,v) is zero unless v <= u and (r+1)v <= a. Otherwise it is the coefficient of q^(a-(r+1)v) in G(u-v+r,r), the Gaussian polynomial. The polynomial G is specified by G(s,0)=1, G(0,k+1)=0, and G(s+1,k+1)=G(s,k+1)+q^(s-k)G(s,k), with natural exponents. This gives finite arithmetic evaluation for every input, including infeasible data.", DescribeRole.Definition),
            Node("ferrersleveltransfer-level-card", "All fixed-endpoint levels", "level_card",
                "The cardinality of Level(r,U,u,v,a) is T_a(u,v). Subtract v from the first r rows and drop the last row; this bijects the legal level with decreasing r-tuples bounded by u-v and total a-(r+1)v. Its inverse adds v and appends v. LiUncu.gauss_rectangle supplies the weight enumerator. Coefficient extraction then counts exactly the required sum fiber. If either guard fails the level is empty. For r=0 the rectangle has no entries and only exponent zero contributes.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
