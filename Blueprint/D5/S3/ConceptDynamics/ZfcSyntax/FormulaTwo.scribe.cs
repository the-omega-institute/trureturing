using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ZfcSyntax;

internal sealed class FormulaTwoDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Selected licensed finite first-order syntax and rewriting support.",
        H("FormulaTwo"),
        Blocks(
            Paragraph(Text("Finite free-variable support and its bound for natural-number variables support closure. Language maps preserve formula constructors, with the original proofs of connective and quantifier preservation.")),
            Paragraph(Text("Exact upstream paths, selected capacity spans, exclusions, modification notices and the Apache-2.0 license are in Library/ConceptDynamics/foundation2026firstorder.md.")),
            Paragraph(Text("This prerequisite API supports later concrete set coding and definition elimination. It does not establish the complete CSA construction or its ZFC conservativity claim.")))));
}
