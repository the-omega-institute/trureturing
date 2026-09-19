using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class MechanicalSlopeSensitivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Mechanical/MechanicalSlopeSensitivity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite numerical slope precision has an exact local cost in actual binary observations.",
        H("Mechanical Slope Sensitivity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mechanical-slope-disagreement"),
                DeclarationHandle.Create(Prefix + "slopeDisagreement"),
                H("Actual word disagreement phases"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the subset of the unit phase interval at which the existing lowerMechanicalWord observations disagree at some time before n. The slope is perturbed while the initial phase and the convention for floor boundaries are held fixed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mechanical-slope-local-law"),
                DeclarationHandle.Create(Prefix + "local_slope_disagreement_law"),
                H("Constructed chamber, exact measure, and correlated bit changes"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every irrational slope strictly between zero and one and every finite horizon, the proof constructs a positive radius using actual distances between its cuts and from the relevant endpoints. Every nonnegative perturbation inside it gives an exact disagreement set: the disjoint swept intervals [1-fract(k*alpha)-k*delta,1-fract(k*alpha)), for k=1 through n. Their Lebesgue measure is delta*n*(n+1)/2. On the k-th interval the actual letter changes by +1 at time k-1, by -1 at time k when that position is observed, and by zero elsewhere. Irrationality, floor carries, interval separation, and measure additivity are derived in the live proof; no noise-region or measure certificate is assumed. The approximating slope need not be irrational. This is a local parameter-sensitivity theorem, not a global error law or an independent bit-noise model. The dyadic precision and joint phase-calibration consumers have separate ordinary proofs in the existing theory volume."))),
                DescribeRole.Theorem))));
}
