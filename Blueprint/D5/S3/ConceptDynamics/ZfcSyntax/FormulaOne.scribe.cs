using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ZfcSyntax;

internal sealed class FormulaOneDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Selected licensed finite first-order syntax and rewriting support.",
        H("FormulaOne"),
        Blocks(
            Paragraph(Text("Finite semiformulas retain arbitrary relation arities, separate free variables and finite bound-variable indices, Boolean connectives and quantifiers. The source supplies negation, structural recursion, complexity and decidable equality under the original decidability hypotheses.")),
            Paragraph(Text("Exact upstream paths, selected capacity spans, exclusions, modification notices and the Apache-2.0 license are in Library/ConceptDynamics/foundation2026firstorder.md.")),
            Paragraph(Text("This prerequisite API supports later concrete set coding and definition elimination. It does not establish the complete CSA construction or its ZFC conservativity claim.")))));
}
