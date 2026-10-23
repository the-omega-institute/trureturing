using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMTriangleCacheDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheData.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Untrusted triangle cache mirrors and all unknown-coordinate transitions",
        H("Untrusted triangle cache mirrors and all unknown-coordinate transitions"),
        Blocks(
            Paragraph(Text("All 41294 original rows are retained. The data proposes 342224 transitions, one for every unknown coordinate and each of its four possible values. The cached integer lower is a literal mirror of the original row lower multiplied by the same scale; it is not an imported minimum. Full finite-domain receipt modules must check all mirror assignments, bounds and action/update equations before the cache consumer uses them.")),
            Node("mirror", "mirror", "Proposed literal row mirror",
                "The total binary mirror tree provides hash, lower and all per-row transition words. Missing-data fallback cannot establish correctness; every actual row is independently checked.", DescribeRole.Definition),
            Node("assignment", "assignment", "Whole original partial event from the small hash",
                "The original base-five decoder is applied to the mirror hash. Unknown coordinates and known outcomes retain exactly the original partial-event semantics.", DescribeRole.Definition),
            Node("lower", "lower", "Literal scaled lower proposal",
                "This reads the small integer field. Its equality with the original row interpreter's exact scaled lower is a complete kernel obligation.", DescribeRole.Definition),
            Node("transition", "transition", "Proposed next row and actual symmetry tag",
                "The selected word supplies a new representative row and action. A later receipt verifies that action on the whole updated assignment, not merely a hash or prefix mask.", DescribeRole.Definition),
            Node("check-mirror-fields", "checkMirrorFields", "Check exact original raw fields once per mirror",
                "The original raw hash and scaled lower are compared to the complete mirror row. The generic checked-raw-mirror theorem earns the entire original assignment equality from these fields.", DescribeRole.Definition),
            Node("check-mirror", "checkMirror", "Compare each mirror with the original row",
                "The Boolean checks equality of the entire partial-assignment function and equality of the exact integer lower with the original row.", DescribeRole.Definition),
            Node("check-transitions", "checkTransitions", "Check all actual unknown-coordinate transitions",
                "Every unknown coordinate and all four outcomes are quantified. The entire new assignment must equal the actual partial action applied to the complete original updated representative.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
