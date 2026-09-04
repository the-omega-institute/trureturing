using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeArenas;

internal sealed class FourthFifthArenasDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite typed arenas for contextual meanings and causal models.",
        H("Fourth and Fifth Information-Escape Arenas"),
        Blocks(
            DefinitionNode("context-fintype", "contextFintype", "Context finite instance",
                "A finite instance obtained through a private equivalence."),
            DefinitionNode("context-decidable-equality", "contextDecidableEq",
                "Context decidable equality",
                "A decidable-equality instance obtained through a private equivalence."),
            DefinitionNode("context-readout", "ContextReadout", "Context readout indices",
                "The readout index type names the context fields, the two fixed-meaning admissions, and their typed axes."),
            DefinitionNode("context-signature", "contextSignature", "Context signature",
                "The typed signature exposes the five context parameters as CUT readouts and the two fixed meanings as ADMIT readouts."),
            DefinitionNode("context-arena", "contextArena",
                "Context-selected fixed-meaning arena",
                "The arena packages BinaryInterpretationContext, contextSignature, and the anchor law separating the selected parameters and meanings."),
            DefinitionNode("model-fintype", "modelFintype", "Causal-model finite instance",
                "A finite instance obtained through a private equivalence."),
            DefinitionNode("model-decidable-equality", "modelDecidableEq",
                "Causal-model decidable equality",
                "A decidable-equality instance obtained through a private equivalence."),
            DefinitionNode("model-readout", "ModelReadout", "Causal-model readout indices",
                "The readout index type separates intervention behavior from counterfactual behavior."),
            DefinitionNode("intervention-signature", "interventionSignature",
                "Intervention signature",
                "The typed signature assigns the Int and CF function types to the two CUT readouts on DeterministicBoolSCM."),
            DefinitionNode("intervention-arena", "interventionArena",
                "Intervention and counterfactual arena",
                "The arena packages DeterministicBoolSCM and requires two models with equal intervention readouts and unequal counterfactual readouts."))));

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
