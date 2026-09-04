using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class TypedStableRightCongruenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every exact finite typed DFAO identification induces a stable right coloring of prefix occurrences, providing a weaker structural target for certified lower bounds.",
        H("Typed Stable Right Colorings"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("identification-induces-stable-right-coloring"),
                DeclarationHandle.Create(
                    "D5/S0/Automata/TypedStableRightCongruence.TypedStableRightColoring.ofIdentification"),
                H("Exact identifications induce typed stable right colorings"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The induced coloring preserves equal prefixes, deterministic equal-symbol extensions, terminal outputs, and the underlying partial-base run. It forgets the explicit transition table while retaining conditions forced by every exact machine."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("stable-right-refutation-excludes-identification"),
                DeclarationHandle.Create(
                    "D5/S0/Automata/TypedStableRightCongruence.no_identification_of_no_stable_right_coloring"),
                H("Refuting the relaxation excludes every exact identification"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Since every exact identification maps into the stable-right-coloring relaxation, emptiness of the relaxation implies emptiness of the exact identification carrier on the same finite color type."))),
                DescribeRole.Theorem)),
        []));
}
