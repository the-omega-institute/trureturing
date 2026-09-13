using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting;

internal sealed class GuardedBoxPathAttainmentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Guarded Box Path Attainment.",
        H("Guarded Box Path Attainment"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("guardedboxpathattainment-exists-shortest-word"),
                DeclarationHandle.Create("D5/S0/Rewriting/GuardedBoxPathAttainment.exists_shortest_word"),
                H("Shortest successful unit words"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite set of natural coordinates with arbitrary natural capacities, any two "
                    + "configurations inside the box can be joined by a successful word of unit increases "
                    + "and decreases. Its length equals the sum of the absolute coordinate differences, "
                    + "and no successful word with the same endpoints is shorter. Moving a coordinate "
                    + "toward its endpoint keeps it between its current value and its target, so every "
                    + "guard succeeds. Each move reduces the remaining distance by one. At distance zero "
                    + "the empty word suffices. Zero-capacity coordinates require no instructions."))),
                DescribeRole.Theorem))));
}
