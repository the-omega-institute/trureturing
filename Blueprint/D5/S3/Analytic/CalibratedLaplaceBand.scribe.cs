using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class CalibratedLaplaceBandDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/CalibratedLaplaceBand.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Calibrated band mass gives an attained linear-noise bound for genuine positive Laplace measures.",
        H("Calibrated Laplace Band"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("calibrated-laplace-band-halfbandtime"),
                DeclarationHandle.Create(Prefix + "halfBandTime"),
                H("Calibrated observation time"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The single observation time log(2)/r; positivity of r is required by its consumers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("calibrated-laplace-band-halfbandtime-spec"),
                DeclarationHandle.Create(Prefix + "halfBandTime_spec"),
                H("Exact kernel calibration"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The chosen time is nonnegative, with kernel values one half at r and one quarter at 2r."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("calibrated-laplace-band-band-mass-lower"),
                DeclarationHandle.Create(Prefix + "band_mass_lower"),
                H("Nested band mass lower bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual Laplace integral dominates a two-step simple function. Both low-band mass and calibrated wider-band mass are retained; no probability or support hypothesis is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("calibrated-laplace-band-normalized-band-feasible-iff-two-atoms"),
                DeclarationHandle.Create(Prefix + "normalized_band_feasible_iff_two_atoms"),
                H("Exact normalized band extremal problem"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary nonnegative observation times and upper envelopes, a prescribed low-energy mass is feasible among probability measures of unit mass in [0,R] exactly when the genuine two-endpoint Bernoulli measure is feasible."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("calibrated-laplace-band-calibrated-half-band-bound"),
                DeclarationHandle.Create(Prefix + "calibrated_half_band_bound"),
                H("One-time linear noise and tail bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If mass([0,2r]) is at least M minus tau and the observed correlation at log(2)/r is at most M/4 plus epsilon, mass([0,r]) is at most 4 epsilon plus tau. These are calibrated data constraints, not assertions about a physical cutoff."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("calibrated-laplace-band-normalized-half-band-sharp"),
                DeclarationHandle.Create(Prefix + "normalized_half_band_sharp"),
                H("Attained normalized noise constant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The probability measure m delta_r plus (1-m) delta_2r has an all-time discrepancy at most m/4 from exp(-2rt), attaining m/4 at the chosen time. Thus the coefficient four is sharp for exact-band probability measures. No sharpness claim is made for the tail coefficient."))),
                DescribeRole.Theorem))));
}
