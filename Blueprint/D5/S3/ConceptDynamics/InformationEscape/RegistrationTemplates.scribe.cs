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
            Paragraph(Text("The separation family serves two gold registrations. Bijection, admitted surjection, anchored separation, context selection, exact design, completion exchange, scope tables, and two-step binary protocols each serve one gold registration and are helpers under the reuse criterion.")),
            DeclarationNode("cut-realization", "cutRealization", "Single CUT realization",
                "One typed function supplies the single CUT readout, with no point anchors."),
            DeclarationNode("bijective-arena", "bijectiveArena", "Bijection helper",
                "The generated law requires bijectivity of the realization's readout."),
            DeclarationNode("separation-realization", "separationRealization", "Separation realization",
                "Two typed functions supply coarse and fine CUT readouts."),
            DeclarationNode("separation-arena", "separationArena", "Separation template",
                "The generated law requires two states with equal coarse readouts and different fine readouts."),
            DeclarationNode("admitted-surjection-realization", "admittedSurjectionRealization",
                "Admitted-surjection realization",
                "A function supplies a CUT readout and a decidable predicate supplies a Boolean ADMIT readout."),
            DeclarationNode("admitted-surjection-arena", "admittedSurjectionArena",
                "Admitted-surjection helper",
                "Every output has an admitted preimage, and two admitted states have distinct outputs."),
            DeclarationNode("anchored-separation-realization", "anchoredSeparationRealization",
                "Anchored-separation realization",
                "Two CUT readouts, two ADMIT predicates, and two point anchors supply the primitive inventory."),
            DeclarationNode("anchored-separation-arena", "anchoredSeparationArena",
                "Anchored-separation helper",
                "The anchors satisfy their admission predicates, agree in one readout, differ in the other, and preclude a recovery map."),
            DeclarationNode("context-selection-realization", "contextSelectionRealization",
                "Context-selection realization",
                "Two shared readouts, three Boolean parameters, two ADMIT predicates, and two anchors supply the context inventory."),
            DeclarationNode("context-selection-arena", "contextSelectionArena",
                "Context-selection helper",
                "The law records agreement of the shared readouts, variation of all three parameters, and admission at the two anchors."),
            DeclarationNode("exact-design-realization", "exactDesignRealization",
                "Exact-design realization", "Two Boolean functions supply the experimental CUT readouts."),
            DeclarationNode("exact-design-arena", "exactDesignArena", "Exact-design helper",
                "Each readout alone is noninjective; the joint readout is injective and requires both experiments."),
            DeclarationNode("completion-exchange-realization", "completionExchangeRealization",
                "Completion-exchange realization",
                "Two state transitions supply FLOW readouts and one observation supplies a CUT readout."),
            DeclarationNode("completion-exchange-arena", "completionExchangeArena",
                "Completion-exchange helper",
                "The law requires noncommuting transitions and different kernels for the two completion orders, using the existing unbounded predictiveProjection."),
            DeclarationNode("scope-table-realization", "scopeTableRealization",
                "Scope-table realization", "Three decidable predicates supply Boolean ADMIT readouts."),
            DeclarationNode("scope-table-arena", "scopeTableArena", "Scope-table helper",
                "Explicit coordinate functions compare the three local marginals; no state satisfies all three admission predicates."),
            DeclarationNode("binary-family-signature", "binaryFamilySignature", "Binary sensor inventory",
                "An arbitrary finite sensor type indexes Boolean CUT readouts over the supplied carrier."),
            DeclarationNode("binary-family-realization", "binaryFamilyRealization", "Binary sensor realization",
                "The supplied sensor family defines the readouts, with no point anchors."),
            DeclarationNode("first-success", "firstSuccess", "First successful natural index",
                "A natural-number predicate has its least successful index when a witness exists, and zero otherwise."),
            DeclarationNode("first-success-eq-find", "firstSuccess_eq_find", "Witnessed minimum transport",
                "An existence witness identifies firstSuccess with Nat.find for the same predicate.", DescribeRole.Theorem),
            DeclarationNode("two-step-statement", "twoStepStatement", "Two-step binary protocol statement",
                "The first sensor divides four named states into pairs. A history-dependent second question identifies the state; individual sensors and smaller depths fail, while adaptive and static costs are two and three."),
            DeclarationNode("two-step-arena", "twoStepArena", "Two-step protocol helper",
                "The supplied finite arena and sensors generate the protocol law with realization-dependent adaptive and static minima."),
            DeclarationNode("two-step-legacy", "twoStepLegacy", "Two-step registration bridge",
                "Existence witnesses transport the two source Nat.find costs to the generated law using firstSuccess_eq_find.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe DeclarationNode(
        string id, string declaration, string title, string paragraph,
        DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            role);
}
