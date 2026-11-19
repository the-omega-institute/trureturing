using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LinearForests;

internal sealed class AlternatingCompletionLawDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Gessel =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/gessel1989cyclerook");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mass and conditioning on a fixed extension event in the uniform alternating full-cycle law.",
        H("The static alternating completion law"),
        Blocks(Describe.Lean(
            DescribeId.Create("alternating-completion-law"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/LinearForests/AlternatingCompletionLaw.alternating_completion_law"),
            H("Exact mass and conditioning for alternating forest completions"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Gessel),
            Blocks(
                Paragraph(Text(
                    "The carrier has n labels of each of two colors, with n positive. "
                    + "The prescribed relation is right-unique, left-unique and acyclic, "
                    + "and its edges change color. Its actual tails and heads correspond "
                    + "to the weak components, including isolates. The alternating completions "
                    + "are in bijection with compatible cycles on these components, with the same "
                    + "tail-to-head connector equation as in the classification theorem.")),
                Paragraph(Text(
                    "Let D be the product of n! and (n−1)!. The uniform probability mass on the "
                    + "actual alternating full cycles of the original carrier assigns 1/D to each cycle. "
                    + "The event of extending all prescribed edges has outer measure M/D, "
                    + "where M counts the actual alternating completions. "
                    + "This event has positive mass exactly when a completion exists.")),
                Paragraph(Text(
                    "For every support witness of the event, filtering the ambient mass is "
                    + "the pushforward along inclusion of a uniform mass on the completions. "
                    + "Under the same completion mass, the pushforward along the endpoint "
                    + "equivalence gives 1/M to every compatible component cycle.")),
                Paragraph(Text(
                    "The specialization of the two-state inventory to opposite target colors "
                    + "counts the ambient cycles. The extension event and the completion subtype "
                    + "have the same underlying permutations. The finite uniform event formula "
                    + "and transport through these equivalences give the stated probabilities."))),
            DescribeRole.Theorem))));
}
