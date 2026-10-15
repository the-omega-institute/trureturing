using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class FiniteLocalRowCacheDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/FiniteLocalRowCache.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact local-row transition cache soundness",
        H("Exact local-row transition cache soundness"),
        Blocks(
            Paragraph(Text("A state associates an original row assignment with an actual partial event through an earned symmetry action. The generic theorem checks an entire transition assignment, transports the actual coordinate fill through the previous action, and composes the new action with the old one. It supplies no concrete table acceptance and does not substitute a producer premise for the actual row checker.")),
            Node("associated", "Associated", "Whole-function row association",
                "The original stored row assignment equals the actual partial action of the earned symmetry on the complete original partial event.", DescribeRole.Definition),
            Node("check-transition", "checkTransition", "Exact entire assignment transition check",
                "The next row assignment must equal the actual next action applied to the original row assignment with this coordinate and value filled.", DescribeRole.Definition),
            Node("step", "step", "Transport the real fill before a row transition",
                "The old action determines the representative coordinate preimage and transformed value. The returned action is composed with the old earned action in the supplied proven order.", DescribeRole.Definition),
            Node("checked-step-associated", "checked_step_associated", "A checked transition preserves the actual association",
                "Actual update and composition laws, the old full association and the complete transition check establish the new full association after the original coordinate fill.", DescribeRole.Theorem),
            Node("associated-lower-bound", "associated_lower_bound", "An accepted original row bounds the original compatible event",
                "Complete actual row acceptance gives a bound on the transported compatible completion. Exact score invariance returns the same bound on the original completion.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
