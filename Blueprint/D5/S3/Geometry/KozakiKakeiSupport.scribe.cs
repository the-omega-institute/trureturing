using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class KozakiKakeiSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/KozakiKakeiSupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For m at least four, counting nonzero evaluations with two specified true coordinates determines whether those columns are adjacent.",
        H("The signed Boolean support recovers adjacency"),
        Blocks(
            Definition("boolNumber", "Boolean evaluation coordinates",
                "False maps to zero and true maps to one in the complex field."),
            Definition("Cuts", "Matching transversals",
                "A Boolean assignment cuts a matching when the two values on every edge differ."),
            Theorem("eval_matching_ne_zero", "Nonzero matching evaluations",
                "An oriented matching polynomial is nonzero on a Boolean assignment exactly when the assignment cuts every matching edge."),
            Theorem("cuts_separate", "Forcing the two endpoints",
                "If an assignment cuts a matching and the two specified columns are both true, those columns lie on distinct matching edges."),
            Theorem("signed_support_recovers_adjacency", "Signed support counts detect edges",
                "For an adjacent pair, one matching admits no cuts with both entries true and the other has exactly 2 to the power m−2. For a nonedge both matchings have that many cuts, with at most one common cut. Removing all possible common cancellations leaves strictly more than the edge count when m is at least four."),
            Theorem("pairSupport_card_invariant", "Scalar symmetry transports support counts",
                "Composition of Boolean assignments with the permutation bijects the two supports. The nonzero scalar preserves the property of evaluating to a nonzero value."),
            Theorem("dihedral_of_scalar_large", "Large-order necessity",
                "Scalar symmetry preserves adjacency by the support count, and the cycle reconstruction forces the relabeling to be dihedral."))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static string NodeId(string name) =>
        "frieze-support-" + name.ToLowerInvariant().Replace('_', '-');
}
