using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class KozakiKakeiCycleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/KozakiKakeiCycle.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two unordered matchings partition the edges of the cycle on the columns.",
        H("Recovering the cycle from its two matchings"),
        Blocks(
            Definition("step", "Cyclic successor",
                "The successor adds one modulo 2m."),
            Definition("Adjacent", "Cycle adjacency",
                "Two columns are adjacent when either is the successor of the other."),
            Definition("SameEdge", "Membership in a matching edge",
                "The two columns form an edge of the given matching in one of its two orders."),
            Theorem("step_val", "Successor index",
                "The value of the successor is the remainder of the index plus one modulo 2m."),
            Theorem("step_ne", "Successor is distinct",
                "The cycle has at least four columns, so its successor has no fixed point."),
            Theorem("adjacent_ne", "Adjacent vertices are distinct",
                "Both orientations of adjacency relate distinct columns."),
            Theorem("odd_forward", "Orientation of odd edges",
                "The second end of every odd matching edge is the successor of its first end."),
            Theorem("even_forward", "Orientation of interior even edges",
                "The second end of each nonclosing even edge is the successor of its first end."),
            Theorem("even_closing", "Orientation of the closing edge",
                "The first end of the closing even edge is the successor of its second end."),
            Theorem("sameEdge_iff", "Recognizing a matching edge",
                "For distinct columns, their inverse images under the matching have the same edge index exactly when they form a matching edge."),
            Theorem("edges_cover", "Cycle edge coverage",
                "An unordered pair of distinct columns is adjacent exactly when it belongs to the odd or even matching."),
            Theorem("edges_disjoint", "Disjoint cycle matchings",
                "An unordered pair of distinct columns cannot be an edge of both matchings."),
            Theorem("dihedral_of_preserves_adjacency", "Exact cycle reconstruction",
                "The images of zero and one select a start and an orientation. Injectivity forces each successive image to use the neighbor different from the preceding image. This determines a rotation or a reflection on the complete cycle."))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static string NodeId(string name) =>
        "frieze-cycle-" + name.ToLowerInvariant().Replace('_', '-');
}
