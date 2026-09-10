using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ZfcEntailment;

internal sealed class CalculusTwoDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Licensed Foundation.Logic.Calculus source for the concrete first-order pair extension.",
        H("CalculusTwo"),
        Blocks(
            Paragraph(Text("Source-command excerpt selected from Foundation.Logic.Calculus, lines 321-376, at Foundation revision 30a16ffa93d79d73ab4d02427fa00f50e039bf29. Only commands with live proof or source-elaboration consumers for the Kuratowski pair extension are retained.")),
            Paragraph(Text("The Lean file retains selected upstream commands and their compiler companions. "
                + "The immutable source map, modification notices, full Apache-2.0 license "
                + "and retirement condition are in Library/ConceptDynamics/foundation2026firstorder.md.")),
            Paragraph(Text("The retained commands supply the formulas, rewriting operations, set operations "
                + "or proof and elaboration machinery used by the concrete pair interpretation. This excerpt does not represent the full upstream module.")))));
}
