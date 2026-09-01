using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics;

internal sealed class ReadoutBlackwellAdapterDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ReadoutBlackwellAdapter.bayesRisk_mono_of_measurable_refinement";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Measurable readout factorization is transported into the existing Blackwell order and Bayes-risk monotonicity.",
        H("Readout Refinement as Blackwell Garbling"),
        Blocks(Describe.Lean(
            DescribeId.Create("readout-blackwell-adapter"),
            DeclarationHandle.Create(Declaration),
            H("Finer measurable readouts have no larger optimal Bayes risk"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Measurable refinement augments the repository factorization preorder with the measurability required to form deterministic kernels.")),
                Paragraph(Text(
                    "Mathlib's deterministic-kernel composition identity turns the factor map into a Blackwell garbling from the finer readout to the coarse readout.")),
                Paragraph(Text(
                    "The existing repository Blackwell theorem then gives Bayes-risk monotonicity for every prior, measurable decision space, and ENNReal-valued loss."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/ConceptDynamics/ConceptJoinUniversal")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Estimation/DecisionRisk/GarblingIncreasesBayesRisk")),
        ]));
}