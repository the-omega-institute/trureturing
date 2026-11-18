using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MaximalHockeyStickCornerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/MaximalHockeyStickCorner.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Common-support compression without invertibility assumptions",
        H("Common-support compression without invertibility assumptions"), Blocks(
            Paragraph(Text("All coordinate and spectral corners are allowed to be empty. These source-owned geometry results implement the common-support localization antecedent credited to GGJ, without importing a general-convex classifier from that literature.")),
            Node("inclusion", "inclusion p is the rectangular coordinate inclusion from the subtype satisfying p into the ambient finite index type. CornerOptimization uses it to extend compressed feasible matrices.", false, false),
            Node("inclusion_isometry", "The adjoint of inclusion p times inclusion p is the identity on the subtype, also for an empty subtype. Compression and extension consume this isometry.", true, false),
            Node("inclusion_projection", "inclusion p times its adjoint is the ambient diagonal indicator of p. This identifies the support projection used to reconstruct a supported matrix.", true, false),
            Node("inclusion_compress", "Adjoint-inclusion times X times inclusion is exactly the subtype submatrix of X. CornerOptimization consumes this identification for feasibility and trace transport.", true, false),
            Node("compress_le", "Loewner inequalities between ambient matrices remain valid on the subtype submatrices. No positivity of each matrix is separately assumed. Optimization reduction uses this order preservation.", true, false),
            Node("extend_le", "Loewner inequalities between subtype matrices remain valid after extension by inclusion and its adjoint. Optimization reduction uses this to construct ambient feasible overlaps.", true, false),
            Node("diagonal_corner_support", "For d_i in [0,1], real t and PSD X below diag(d) and t(1-diag(d)), the diagonal indicator P of 0<d_i<1 satisfies PX=X and XP=X. Endpoint columns vanish by positivity. The conclusion does not assume t>0; feasibility supplies the necessary restrictions.", true, false),
            Node("overlap_supported", "For any PSD contraction C, any real t and X in positiveOverlaps C (t(1-C)), P=interiorProjection C satisfies PX=X and XP=X. Spectral diagonalization transfers the coordinate support argument. SingularCriterion and optimization reduction use this exact common corner.", true, false))));

    private static DocumentBlock Node(string name, string prose, bool theorem, bool literature) =>
        Describe.Lean(DescribeId.Create("maximal-hockey-stick-corner-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name.Replace("_", " ")),
            StatementSource.WithoutFormula(),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
}
