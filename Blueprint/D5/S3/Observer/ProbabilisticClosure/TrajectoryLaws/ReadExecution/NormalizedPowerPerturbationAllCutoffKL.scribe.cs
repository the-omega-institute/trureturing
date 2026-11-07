using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution;

internal sealed class NormalizedPowerPerturbationAllCutoffKLDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "WIP: normalized countable power perturbations and every finite collapsed cutoff.",
        H("Normalized power perturbations: all-cutoff KL bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normalized-power-perturbation-all-cutoff-kl"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/NormalizedPowerPerturbationAllCutoffKL.normalized_power_perturbation_all_cutoff_kl"),
                H("Normalized countable power perturbations have a two-reference all-cutoff KL bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "WIP statement for the E3 source atom. For an exponent m at least four, " +
                        "a nonnegative perturbation d with d(k) at most delta times k^(m-1) " +
                        "is added to the positive-index power-exponential law. The normalizers " +
                        "are the exact infinite sums. Both normalized laws have zero mass at k=0, " +
                        "positive mass at every positive k, and the two reference square energies " +
                        "are bounded by 4 delta^2 (1-exp(-s))^2.")),
                    Paragraph(Text(
                        "For every finite L, the carrier is Option(Fin L): r maps to the physical " +
                        "count r.val+1 and none is the complete remaining tail. The resulting " +
                        "finite KL divergences in both directions are at most " +
                        "4 delta^2 s^2 min(1,(sL)^(m-1)). The source neighborhood lower bound " +
                        "is stated through the exact factorial-normalizer inequality hZ.")),
                    Paragraph(Text(
                        "The declaration is intentionally WIP and remains open pending a kernel proof " +
                        "of the countable normalized energy estimate and the finite-to-countable tail " +
                        "Cauchy passage. No source-specific polynomial, finite cutoff, truncated " +
                        "normalizer, sign assumption, or auxiliary stopping premise is introduced."))))),
                DescribeRole.Theorem))));
}
