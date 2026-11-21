using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class KozakiKakeiFourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/KozakiKakeiFour.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At four columns the two signed evaluations of a pair indicator separate edges and diagonals directly.",
        H("The signed four-column branch"),
        Blocks(
            Theorem("signed_four_evaluation", "The signed quadratic on pairs",
                "The indicator of two distinct columns gives one on edges and minus two on diagonals."),
            Theorem("dihedral_of_scalar_four", "Four-column necessity",
                "Among the images of the two edges incident with a fixed vertex, at least one is an edge. The scalar must be one, so every edge maps to an edge."),
            Theorem("dihedral_of_preservesLevel", "Necessity on the whole size range",
                "Apply scalar rigidity to the admissible constant matrices. Then use signed pair evaluations for m equal to two and recovery by support counts for every m at least four."))));

    private static DocumentBlock Theorem(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static string NodeId(string name) =>
        "frieze-four-" + name.ToLowerInvariant().Replace('_', '-');
}
