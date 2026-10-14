using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class FiniteSharedLocalBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/FiniteSharedLocalBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shared local readouts with actual projection checks",
        H("Shared local readouts with actual projection checks"),
        Blocks(
            Paragraph(Text("A finite table shares checked local row and symmetry-action readouts. Each readout proposes a complete transported partial assignment and a lower value. The lookup tables must agree with all original certificate rows, whose full acceptance and score invariance remain explicit premises. Sharing a readout never identifies distinct global partial contexts.")),
            Node("readout", "Readout", "Original row, action and proposed readout",
                "The state names the original row and complete action; the assignment and lower are untrusted proposals until checked.", DescribeRole.Definition),
            Node("check-readout", "checkReadout", "Check the full transported assignment and original lower",
                "The complete original row assignment must equal the actual partial action of the proposed state. Its original lower must equal the proposed readout lower.", DescribeRole.Definition),
            Node("checked-readout-lower", "checked_readout_lower", "A checked shared readout bounds every compatible completion",
                "Original local-row acceptance and exact lookup equalities establish row/action association. Score invariance transports the original lower bound to every completion of the entire readout assignment.", DescribeRole.Theorem),
            Node("check-selection", "checkSelection", "Check each selected actual projection",
                "Each global placement independently compares its actual projected partial assignment with the entire selected readout assignment.", DescribeRole.Definition),
            Node("checked-selection-sum", "checked_selection_sum_lower", "Sum all selected local bounds on the original event",
                "Accepted local readouts and every actual projection check prove that the sum of selected lower values bounds the sum of the original local scores on every compatible global event.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
