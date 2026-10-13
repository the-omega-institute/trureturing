using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMCacheSoundnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full original-block cache association and score bounds",
        H("Full original-block cache association and score bounds"),
        Blocks(
            Paragraph(Text("Validity ties every stored literal to its indexed mirror and every original row assignment to the earned action on the entire actual block projection. The complete row and transition receipts discharge the concrete obligations of the generic local cache theorem. Original local row acceptance and actual score invariance then bound each original block of every compatible complete event.")),
            Node("AssociatedCache", "AssociatedCache", "All thirty-two actual block associations",
                "Both local validity families quantify over every original block, with its actual original marginal map. Exact full assignments remain in the invariant.", DescribeRole.Definition),
            Node("triangle-step-valid", "triangle_step_valid", "Preserve triangle association after an actual unknown fill",
                "The actual inverse law preserves unknownness in representative coordinates. The full transition receipt and generic composition/update theorem then prove the new original-row association and mirror equality.", DescribeRole.Theorem),
            Node("singleton-step-valid", "singleton_step_valid", "Preserve singleton association after an actual unknown fill",
                "This consumes every corresponding singleton law and receipt, with the same whole-function association invariant.", DescribeRole.Theorem),
            Node("step-associated", "step_associated", "Preserve the complete original global cache",
                "Incidence case analysis uses the exact projection-update law. Every affected original block receives a checked local transition; every unaffected block retains its full association.", DescribeRole.Theorem),
            Node("initial-associated", "initial_associated", "Earn all original all-unknown associations",
                "Actual mirror-root receipts and identity-action proofs establish each initial original block relation. The literal lower and row data receive the same indexed mirror invariant.", DescribeRole.Theorem),
            Node("associated-lower-le-score", "associated_lower_le_score", "An associated cache bounds the unchanged exact score",
                "Generic accepted-local-row soundness transports every compatible completion by its earned action. Exact score invariance and literal lower equality yield each actual block bound; finite-sum monotonicity combines all original thirty-two blocks.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
