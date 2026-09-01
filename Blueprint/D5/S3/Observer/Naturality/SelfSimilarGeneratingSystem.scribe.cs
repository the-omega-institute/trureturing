using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Naturality;

internal sealed class SelfSimilarGeneratingSystemDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Observer/Naturality/SelfSimilarGeneratingSystem.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A generating system combines six structural components with geometric and "
            + "observer-compatible self-similarity laws.",
        H("Self-Similar Generating Systems"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("self-similar-generating-system"),
                DeclarationHandle.Create(DeclarationPrefix + "System"),
                H("Geometric and generative self-similarity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The system carries a state carrier, a family of branches, a "
                            + "reflection or duality, a positive region, a scale-indexed "
                            + "observation interface, and a completion operation. A represented "
                            + "branch at each scale supplies the second displayed law.")),
                    Paragraph(Text(
                        "Geometric self-similarity requires the union of all branch images to "
                            + "cover the carrier. Generative self-similarity requires every "
                            + "observation map to semiconjugate each branch to its represented "
                            + "branch at that scale.")),
                    Paragraph(Text(
                        "All components and both laws are jointly realizable on the two-point "
                            + "Boolean carrier. The one branch, reflection, observation, "
                            + "completion, and represented branch are identities, while the "
                            + "positive region is the whole carrier.")),
                    Paragraph(Text(
                        "The source gives no involutivity, cone algebra, or completion "
                            + "idempotence axioms. Its closing philosophical description adds no "
                            + "further mathematical condition, so none of these claims is "
                            + "formalized.")),
                    Paragraph(Text(
                        "Repository and pinned-package searches found concrete self-similar "
                            + "sets and generic semiconjugacy components, but no aggregate "
                            + "structure with these six components and both laws."))),
                DescribeRole.Definition))));
}
