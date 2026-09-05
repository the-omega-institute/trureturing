using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeRealizations;

internal sealed class UnifiedCausalRegistrationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two frozen causal transitions are registered on the unified arena for import-closure consumers.",
        H("Unified Causal Registration"),
        Blocks(
            Paragraph(Text(
                "The observation-intervention and intervention-counterfactual separation theorems share the canonical unifiedArena under the unifiedCausal catalog identity.")),
            Paragraph(Text(
                "Each occurrence uses its branch-local primitive bundle and faithful realization from UnifiedCausalAlignment. The cumulative three-readout analysis catalog is separate from these two theorem occurrences.")),
            Paragraph(Text(
                "Importing this module makes both registrations persist with UnifiedCausalRegistration as their contributor. This module does not seal a root or declare an expected occurrence manifest.")))));
}
