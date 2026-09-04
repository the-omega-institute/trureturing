using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeArenas;

internal sealed class EndStateOmitsPreemptingCauseDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered preemption is expressed through endpoint, cause, admission, and anchor primitives.",
        H("End State Omits Preempting Cause Arena"),
        Blocks(
            Node("mechanism-equivalence", "mechanismEquiv", "Boolean mechanism equivalence",
                "The equivalence exhaustively identifies the two source mechanisms with Boolean values."),
            Node("mechanism-fintype", "instFintypeMechanism", "Finite source mechanisms",
                "This is the finite/decidable-equality instance obtained through a private equivalence."),
            Node("ordered-preemption-decidable", "instDecidableIsOrderedPreemption",
                "Decidable ordered preemption",
                "This decidability instance is obtained by unfolding the finite ordered-preemption predicate."),
            Node("preemption-readout", "PreemptionReadout", "Preemption readout indices",
                "The finite index type names the two CUT and two ADMIT readouts."),
            Node("preemption-readout-decidable-equality", "instDecidableEqPreemptionReadout",
                "Decidable equality for preemption readouts",
                "This is the finite/decidable-equality instance obtained through a private equivalence."),
            Node("preemption-readout-fintype", "instFintypePreemptionReadout",
                "Finite preemption readouts",
                "This is the finite/decidable-equality instance obtained through a private equivalence."),
            Node("preemption-anchor", "PreemptionAnchor", "Preemption anchor indices",
                "The finite anchor type names the two source trace witnesses."),
            Node("preemption-anchor-decidable-equality", "instDecidableEqPreemptionAnchor",
                "Decidable equality for preemption anchors",
                "This is the finite/decidable-equality instance obtained through a private equivalence."),
            Node("preemption-anchor-fintype", "instFintypePreemptionAnchor",
                "Finite preemption anchors",
                "This is the finite/decidable-equality instance obtained through a private equivalence."),
            Node("preemption-signature", "preemptionSignature", "Typed preemption signature",
                "The signature assigns endpoint and active-cause CUTs, two Boolean ADMITS, and both trace anchors."),
            Node("end-state-preemption-statement", "EndStateOmitsPreemptingCauseStatement",
                "Frozen preemption statement type",
                "This alias is definitionally the type of the frozen theorem D5/S3/ConceptDynamics/Attribution/EndStateOmitsPreemptingCause.end_state_omits_preempting_cause."),
            Node("end-state-preemption-arena", "endStateOmitsPreemptingCauseArena",
                "Preemption trace arena",
                "Two CUTs and two coded ADMITS are evaluated at the named trace anchors, including the endpoint-factorization obstruction."))));

    private static DocumentBlock.Describe Node(
        string id, string declaration, string title, string explanation) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))),
            DescribeRole.Definition);
}
