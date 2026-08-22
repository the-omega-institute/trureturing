using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Epistemic;

internal sealed class EpistemicChangeTrichotomyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-world conclusion changes expose an admission, evidence, or inference change.",
        H("Epistemic Change Trichotomy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("epistemic-change-trichotomy"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Epistemic/EpistemicChangeTrichotomy."
                        + "changed_conclusion_exposes_epistemic_component"),
                H("Changed conclusions expose an epistemic component"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The admission predicates, evidence concepts, inference rules, worlds, "
                            + "and conclusion evaluator are independent source primitives.")),
                    Paragraph(Text(
                        "The public fixed-world premise holds the underlying state constant. "
                            + "If every component were also equal, deterministic evaluation "
                            + "would force equal conclusions, contradicting the other premise.")),
                    Paragraph(Text(
                        "The three public alternatives directly audit a change to admissible "
                            + "worlds, evidence distinctions, or the inference rule; no target-"
                            + "defined state structure or private classification is used."))),
                DescribeRole.Theorem))));
}
