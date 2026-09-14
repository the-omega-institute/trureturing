using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class ReifierTriggerRejectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Content-plane probe of rejected statement specialization through the reifier.",
        H("ReifierTriggerReject"),
        Blocks(
            Paragraph(Text("The descriptor fixes the substitution label to zero, while the frozen compatibility theorem quantifies over every label. Exact statement identity must reject this attempted registration.")),
            Paragraph(Text("Expected probe verdict: Canonical Lean report production fails with P1.StatementIdentityMismatch and admission is not reached or is red. The failed command leaves no registry row or generated declaration. This module is not deposited or frozen.")))));
}
