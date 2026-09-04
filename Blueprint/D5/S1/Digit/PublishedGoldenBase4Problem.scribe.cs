using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class PublishedGoldenBase4ProblemDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The published golden-ratio base-four DFAO problem is the exact sparse power specification restricted to Zeckendorf-typed machines with a start-state zero loop and zero-output anchor.",
        H("Published Golden Base-Four DFAO Problem"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("published-global-model-restricts-to-finite-prefix"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/PublishedGoldenBase4Problem.global_model_at_most_implies_prefix_model_at_most"),
                H("Every bounded published global model fits every finite prefix"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The theorem is the finite-to-infinite restriction used by certificate arguments. It retains the published zero-loop and zero-anchor machine evidence while restricting global correctness to a genuine finite family of power inputs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("published-class-forgets-to-wider-typed-class"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/PublishedGoldenBase4Problem.hasGlobalModelAtMost_implies_typed_hasGlobalModelAtMost"),
                H("Published models embed in the wider typed powers-only class"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Forgetting the anchor and zero-loop evidence preserves the underlying globally correct typed machine. The implication is intentionally one-way, so a published-class refutation is never promoted to the wider class without an additional theorem."))),
                DescribeRole.Theorem)),
        []));
}
