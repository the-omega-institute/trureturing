using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class ExactExpansiveConjugacyDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/ExactExpansiveConjugacy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conjugacy of exact positively expansive dynamics",
        H("Conjugacy of exact positively expansive dynamics"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exact-positive-expansivity-conjugacy"),
                DeclarationHandle.Create(Owner + "exact_expansive_conjugate"),
                H("Transport under a compact metric homeomorphism"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The homeomorphism carries images of open sets through iterates. Uniform continuity of its inverse controls all forward times at one common scale and preserves the singleton Bowen property."))),
                DescribeRole.Theorem))));
}
