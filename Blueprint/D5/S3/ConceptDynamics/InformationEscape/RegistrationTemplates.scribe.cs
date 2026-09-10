using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class RegistrationTemplatesDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscape/RegistrationTemplates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Typed constructors generate primitive inventories and laws over explicit canonical arenas.",
        H("Registration Template and Helpers"),
        Blocks(
            Paragraph(Text("The separation family serves two gold registrations. Bijection, admitted surjection, anchored separation, context selection, exact design, completion exchange, and scope tables each serve one gold registration and are helpers under the reuse criterion.")),
            DefinitionNode("cut-realization", "cutRealization", "Single CUT realization",
                "One typed function supplies the single CUT readout, with no point anchors."),
            DefinitionNode("bijective-arena", "bijectiveArena", "Bijection helper",
                "The generated law requires bijectivity of the realization's readout."),
            DefinitionNode("separation-realization", "separationRealization", "Separation realization",
                "Two typed functions supply coarse and fine CUT readouts."),
            DefinitionNode("separation-arena", "separationArena", "Separation template",
                "The generated law requires two states with equal coarse readouts and different fine readouts."),
            DefinitionNode("admitted-surjection-realization", "admittedSurjectionRealization",
                "Admitted-surjection realization",
                "A function supplies a CUT readout and a decidable predicate supplies a Boolean ADMIT readout."),
            DefinitionNode("admitted-surjection-arena", "admittedSurjectionArena",
                "Admitted-surjection helper",
                "Every output has an admitted preimage, and two admitted states have distinct outputs."),
            DefinitionNode("anchored-separation-realization", "anchoredSeparationRealization",
                "Anchored-separation realization",
                "Two CUT readouts, two ADMIT predicates, and two point anchors supply the primitive inventory."),
            DefinitionNode("anchored-separation-arena", "anchoredSeparationArena",
                "Anchored-separation helper",
                "The anchors satisfy their admission predicates, agree in one readout, differ in the other, and preclude a recovery map."),
            DefinitionNode("context-selection-realization", "contextSelectionRealization",
                "Context-selection realization",
                "Two shared readouts, three Boolean parameters, two ADMIT predicates, and two anchors supply the context inventory."),
            DefinitionNode("context-selection-arena", "contextSelectionArena",
                "Context-selection helper",
                "The law records agreement of the shared readouts, variation of all three parameters, and admission at the two anchors."),
            DefinitionNode("exact-design-realization", "exactDesignRealization",
                "Exact-design realization", "Two Boolean functions supply the experimental CUT readouts."),
            DefinitionNode("exact-design-arena", "exactDesignArena", "Exact-design helper",
                "Each readout alone is noninjective; the joint readout is injective and requires both experiments."),
            DefinitionNode("completion-exchange-realization", "completionExchangeRealization",
                "Completion-exchange realization",
                "Two state transitions supply FLOW readouts and one observation supplies a CUT readout."),
            DefinitionNode("completion-exchange-arena", "completionExchangeArena",
                "Completion-exchange helper",
                "The law requires noncommuting transitions and different kernels for the two completion orders, using the existing unbounded predictiveProjection."),
            DefinitionNode("scope-table-realization", "scopeTableRealization",
                "Scope-table realization", "Three decidable predicates supply Boolean ADMIT readouts."),
            DefinitionNode("scope-table-arena", "scopeTableArena", "Scope-table helper",
                "Explicit coordinate functions compare the three local marginals; no state satisfies all three admission predicates."))));

    private static DocumentBlock.Describe DefinitionNode(
        string id, string declaration, string title, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);
}
