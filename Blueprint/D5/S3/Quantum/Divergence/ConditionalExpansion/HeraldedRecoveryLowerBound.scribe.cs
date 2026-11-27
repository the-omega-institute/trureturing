using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence.ConditionalExpansion;

internal sealed class HeraldedRecoveryLowerBoundDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Quantum/Divergence/ConditionalExpansion/HeraldedRecoveryLowerBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite heralded exact recovery gives a universal conditional trace-gap comparison.",
        H("Heralded recovery lower bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("heralded-recovery-contrast-lower-bound"),
                DeclarationHandle.Create(Module + "heralded_recovery_contrast_lower_bound"),
                H("Contrast lower bound from a heralded exact branch"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let N be a finite quantum channel, K a finite Kraus family with effect "
                    + "sum KⱼᴴKⱼ ≤ I, and p ∈ [0,1]. If the Kraus branch sends act N(X) to pX "
                    + "for every matrix X, then every Hermitian amplified test H satisfies "
                    + "p times the positive-trace contrast of H over its reference marginal "
                    + "is at most the corresponding contrast after amp N. The proof includes "
                    + "the failure branch I − sum KⱼᴴKⱼ and uses positive-part trace monotonicity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("heralded-recovery-coefficient-comparison"),
                DeclarationHandle.Create(Module + "heralded_recovery_coefficient_comparison"),
                H("Coefficient comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite channel N on input dimension d ≥ 2, let pRec be the "
                        + "supremum of finite trace-nonincreasing Kraus recovery weights and η "
                        + "the infimum of the admissible conditional ratios. For every γ ≥ 1 "
                        + "and either orthogonality flag, pRec ≤ η ≤ d² pRec. Moreover η is "
                        + "positive exactly when some admissible recovery has positive weight.")),
                    Paragraph(Text(
                        "The coefficient uses the conditional expansion of Hirche, George, "
                        + "Nuradha and Wilde, arXiv:2608.27171v1, Eq. (2.42). Bény and "
                        + "Oreshkov's postprocessing duality, arXiv:1103.0649v3, Theorem 2, "
                        + "gives the complementary-channel characterization of exact recovery."))),
                DescribeRole.Theorem))));
}
