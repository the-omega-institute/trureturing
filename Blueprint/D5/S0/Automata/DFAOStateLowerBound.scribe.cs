using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class DFAOStateLowerBoundDocument : IScribeDocumentDefinition
{
    private const string Declaration = "D5/S0/Automata/DFAOStateLowerBound.state_lower_bound_of_distinguishing_family";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite distinguishing continuations give checkable state lower bounds for output automata built on Mathlib DFA.",
        H("DFAO State Lower Bounds"),
        Blocks(Describe.Lean(
            DescribeId.Create("dfao-state-lower-bound"),
            DeclarationHandle.Create(Declaration),
            H("Distinguishing continuations force distinct reached states"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A DFAO reuses Mathlib's deterministic finite automaton as its transition carrier and adds one output map on states. Correctness may be restricted to an explicitly declared sparse language.")),
                Paragraph(Text(
                    "A finite certificate chooses prefixes and a legal pair-specific continuation for every two distinct indices. The target outputs after that common continuation must differ.")),
                Paragraph(Text(
                    "If two certified prefixes reached the same machine state, the upstream append evaluation law would force the same final state and output after their shared continuation. Correctness would contradict the certificate, so the reached-state map is injective and the state count is bounded below."))),
            DescribeRole.Theorem))));
}