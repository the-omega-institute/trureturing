using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.WeylChronology;

internal sealed class GoldenRobustCalibrationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/WeylChronology/GoldenRobustCalibration.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded Ramsey calibration errors preserve chronology separation when the nominal fringe gap exceeds a certified deterministic budget.",
        H("Golden Robust Ramsey Calibration"),
        Blocks(
            Paragraph(Text(
                "The module adds no stochastic noise law. It exposes five experiment-facing "
                    + "coordinates: baseline, visibility, coupling, phase offset and a "
                    + "probability-level closure/readout residual. The residual is a coarse "
                    + "certified interface and is not claimed to be derived from a particular "
                    + "wavefunction norm.")),
            Paragraph(Text(
                "The perturbation estimate consumes Mathlib's one-Lipschitz sine bound and "
                    + "the preceding ideal visibleChronologyFringe. Separate calibration "
                    + "records may be supplied for the two words, so bounded run-to-run drift "
                    + "is included without assuming independence or a Gaussian model.")),
            Paragraph(Text(
                "Experimental motivation is direct. Tomita et al., Nature Communications 17, "
                    + "4727 (2026), DOI 10.1038/s41467-026-73348-x, report imperfect Ramsey "
                    + "visibility, wrapped phase and projection-noise-limited readout. You et "
                    + "al., Scientific Reports 16, 18474 (2026), DOI "
                    + "10.1038/s41598-026-49820-5, fit coherent phase modulation and heating "
                    + "in spin-echo Ramsey data.")),
            Describe.Lean(
                DescribeId.Create("calibration"),
                DeclarationHandle.Create(Prefix + "RamseyCalibration"),
                H("Ramsey nuisance calibration record"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "One acquisition records baseline, visibility, coupling, phase offset and closure/readout residual explicitly."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ideal-calibration"),
                DeclarationHandle.Create(Prefix + "idealCalibration"),
                H("Ideal calibration"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The ideal record has baseline one half, zero phase offset and zero closure residual."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("robust-fringe"),
                DeclarationHandle.Create(Prefix + "robustChronologyFringe"),
                H("Perturbed chronology fringe"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The plus-port probability is the calibrated baseline plus a visibility-scaled sine of the perturbed chronology phase and the closure residual."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("deviation-budget"),
                DeclarationHandle.Create(Prefix + "calibrationDeviationBudget"),
                H("Certified word-level calibration budget"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The budget adds baseline and closure errors, half the visibility error, and a nominal-visibility-weighted phase error containing both coupling mismatch and phase offset."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ideal-specialization"),
                DeclarationHandle.Create(Prefix + "robust_fringe_ideal_calibration"),
                H("The robust model contains the ideal model"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At the ideal calibration record the robust fringe is exactly the preceding visible chronology fringe."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("deviation-bound"),
                DeclarationHandle.Create(Prefix + "robust_fringe_deviation_le"),
                H("One-word deterministic perturbation bound"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The absolute deviation from the nominal fringe is bounded by the certified budget. The only analytic input is the one-Lipschitz property of sine."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pair-lower-bound"),
                DeclarationHandle.Create(Prefix + "robust_pair_separation_lower_bound"),
                H("Robust pair separation lower bound"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The actual pair gap is at least the nominal pair gap minus the two word-level calibration budgets, even when the two acquisitions use different calibration records."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("margin-survival"),
                DeclarationHandle.Create(Prefix + "robust_fringe_ne_of_nominal_margin"),
                H("Positive nominal margin survives bounded calibration error"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If the nominal fringe gap strictly exceeds the sum of the two certified budgets, every allowed pair of perturbed fringes remains distinct."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The next statistical step is to convert a positive robust fringe margin into "
                    + "a robust total-variation or Bhattacharyya bound using existing generic "
                    + "testing owners. No new concentration theorem should be introduced "
                    + "before that reuse audit is complete."))))));
}
