using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class PositiveLaplaceGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/PositiveLaplaceGap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual positive Laplace integrals give quantitative low-energy bounds and a sharp half-gap noise floor.",
        H("Positive Laplace Gap"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-laplace-gap-laplacecorrelation"),
                DeclarationHandle.Create(Prefix + "laplaceCorrelation"),
                H("Positive Laplace correlation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Bochner integral of exp(-t E) against a genuine measure on nonnegative energies. Finite-measure integrability at nonnegative times is proved privately."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("positive-laplace-gap-low-energy-mass-le"),
                DeclarationHandle.Create(Prefix + "low_energy_mass_le"),
                H("Finite-time low-energy mass bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("From one one-sided envelope at time t >= 0, obtain mass([0,r]) <= K exp(-(Delta-r)t) + epsilon exp(rt). The lower bound comes from the actual integral and Mathlib Markov inequality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-laplace-gap-subthreshold-mass-eq-zero"),
                DeclarationHandle.Create(Prefix + "subthreshold_mass_eq_zero"),
                H("Exact subthreshold exclusion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every r < Delta, all-time noiseless decay with nonnegative prefactor forces the actual measure of [0,r] to vanish. The conclusion is a measure equality, not an arbitrary spectral-mass predicate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-laplace-gap-sharp-half-gap-upper"),
                DeclarationHandle.Create(Prefix + "sharp_half_gap_upper"),
                H("Sharp half-gap noise bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For r > 0 and 0 < b <= a, an envelope a^2 exp(-2rt) + b^2 bounds the low-energy mass by 2ab. The proof evaluates at log(a/b)/r. This is sharp over finite positive measures, with no prescribed total mass."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-laplace-gap-laplace-smul-dirac"),
                DeclarationHandle.Create(Prefix + "laplace_smul_dirac"),
                H("Positive atom evaluation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact Laplace transform of a positively weighted Dirac measure; used by the extremizer."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-laplace-gap-low-mass-feasible-iff-single-atom"),
                DeclarationHandle.Create(Prefix + "low_mass_feasible_iff_single_atom"),
                H("Exact single-atom feasibility reduction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any family of nonnegative-time upper bounds, a given low-energy mass is feasible among all finite positive measures exactly when the single atom at the threshold with that mass is feasible. This yields a complete extremal reduction, without prescribing total mass."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-laplace-gap-half-gap-extremizer"),
                DeclarationHandle.Create(Prefix + "half_gap_extremizer"),
                H("Attained half-gap bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite measure (2ab) delta_r has low-energy mass 2ab and satisfies the envelope for every real time, by a nonnegative square. No sharpness claim under probability normalization is made."))),
                DescribeRole.Theorem))));
}
