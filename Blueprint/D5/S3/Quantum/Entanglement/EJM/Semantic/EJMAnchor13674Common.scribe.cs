using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Semantic;

internal sealed class EJMAnchor13674CommonDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Semantic/EJMAnchor13674Common.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cache assignment and compatibility tools for semantic EJM factors",
        H("Cache assignment and compatibility tools for semantic EJM factors"),
        Blocks(
            Paragraph(Text("These helpers support the actual triangle and singleton factor bounds used by the semantic cut assemblies. They retain the original cached row, local symmetry and projection into the twenty-coordinate event.")),
            Node("mk-triangle", "mkTriangle", "Build the complete triangle cache entry from its state",
                "An index among 41294 triangle states and a local symmetry determine a CachedLocal entry using the original triangle mirror row.", DescribeRole.Definition),
            Node("mk-singleton", "mkSingleton", "Build the complete singleton cache entry from its state",
                "An index among 8689 singleton states and a local symmetry determine a CachedLocal entry using the original singleton mirror row.", DescribeRole.Definition),
            Node("triangle-from-assignment", "triangle_from_assignment", "An exact transformed assignment gives triangle validity",
                "If the triangle cache assignment at the state index equals the local-symmetry action on the supplied ten-coordinate partial assignment, mkTriangle satisfies TriangleValid for that partial assignment. The proof uses the original assignment_eq receipt.", DescribeRole.Theorem),
            Node("singleton-from-assignment", "singleton_from_assignment", "An exact transformed assignment gives singleton validity",
                "If the singleton cache assignment at the state index equals the local-symmetry action on the supplied nine-coordinate partial assignment, mkSingleton satisfies SingletonValid for it.", DescribeRole.Theorem),
            Node("compatible-fill", "compatible_fill", "Fill a coordinate from the same compatible event",
                "Compatibility of a partial assignment with an event is preserved by updating any coordinate to that event value. The proof treats the updated coordinate and all distinct coordinates separately.", DescribeRole.Theorem),
            Node("compatible-project", "compatible_project", "Project both partial and complete assignments together",
                "For any finite coordinate projection into the original twenty coordinates, compatibility is preserved by composing both the partial assignment and event with the same projection.", DescribeRole.Theorem),
            Node("checked-finite-table-merge-lower", "checked_finite_table_merge_lower", "Add two lower bounds on the same compatible event",
                "For arbitrary coordinate and value types, an exact pointwise sum equation for a merged table and lower bounds for both summands on a common partial assignment imply that the merged value is at most the sum of their scores on each compatible event. This helper states the same-event requirement explicitly.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
