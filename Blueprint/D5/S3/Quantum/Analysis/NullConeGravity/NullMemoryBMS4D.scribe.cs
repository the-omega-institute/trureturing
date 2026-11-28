using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class NullMemoryBMS4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.";
    private static readonly LibraryNoteRef NullLocal =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");
    private static readonly LibraryNoteRef NullCone =
        LibraryNoteRef.Create("D5/L/HilbertOperators/chandrasekaran2026nullcone");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sphere-averaged Bondi flux gives an exact mass balance. The angular memory spectrum has four translation modes, and a nonzero zero-frequency value forces a logarithmic infrared divergence.",
        H("Bondi flux and the infrared memory spectrum"),
        Blocks(
            Paragraph(Text("The setting uses the round celestial sphere and a complex news profile. "
                + "Satishchandran and Sorce give the characteristic graviton reference, and "
                + "Chandrasekaran studies radiative gravitational data on intersecting null cones. "
                + "The normalized Bondi mass equation is imposed on the profile. "
                + "The angular part of the Christodoulou memory model is specified by its harmonic eigenvalues.")),
            Entry("bondi-flux", "bondiFlux", "Sphere-averaged news flux",
                "Integrate the squared complex norm of the news on the round sphere and divide by its area 4π.",
                DescribeRole.Definition),
            Entry("flux-nonnegative", "bondiFlux_nonneg", "Nonnegative news flux",
                "The squared norm is pointwise nonnegative and the area normalization is positive."),
            Entry("flux-zero", "bondiFlux_eq_zero_iff", "Zero flux for continuous news",
                "For continuous news the flux vanishes exactly when the profile vanishes everywhere. "
                + "A nonzero value would remain bounded away from zero on an open set of positive round measure."),
            Entry("mass-monotone", "bondi_mass_loss_nonpos", "Bondi mass monotonicity",
                "A mass with derivative equal to minus the news flux at each time is antitone."),
            Entry("energy-balance", "bondi_energy_balance", "Integrated mass balance",
                "For a continuously differentiable mass obeying the mass equation, the mass at a minus "
                + "the mass at b equals the oriented integral of the news flux from a to b."),
            Entry("energy-nonnegative", "bondi_energy_radiated_nonneg", "Nonnegative radiated energy",
                "For a ≤ b the integral of the news flux from a to b is nonnegative."),
            Entry("mass-strict", "bondi_strict_mass_loss_of_nonzero_news", "Strict mass decrease",
                "Suppose the mass equation holds and the news is jointly continuous. If it is nonzero "
                + "as an angular profile at an interior time between a and b, then the mass at b "
                + "is strictly less than at a. The flux stays positive on an interval around that time."),
            Entry("elliptic-eigenvalue", "memoryEllipticEigenvalue", "Memory elliptic eigenvalue",
                "In degree ℓ the eigenvalue of the spherical harmonic model for D²(D² + 2) "
                + "is ℓ(ℓ + 1)(ℓ − 1)(ℓ + 2).",
                DescribeRole.Definition),
            Entry("elliptic-kernel", "memoryElliptic_zero_iff", "Translation kernel",
                "The eigenvalue vanishes exactly in degrees zero and one."),
            Entry("elliptic-positive", "memoryElliptic_pos_iff", "Positive supertranslation modes",
                "The eigenvalue is positive exactly in degrees at least two."),
            Entry("translation-dimension", "poincare_translation_dim_eq_four", "Translation multiplicity",
                "The four-dimensional harmonic multiplicity is 2ℓ + 1. The two kernel degrees therefore "
                + "have total multiplicity 1 + 3 = 4."),
            Entry("green-summability", "memoryGreenSq_summable", "Square-summable inverse eigenvalues",
                "Starting at degree two, the multiplicity divided by the squared eigenvalue is summable. "
                + "The eigenvalue is at least ℓ⁴/2 and the multiplicity is at most 3ℓ, giving the "
                + "summable bound 12/ℓ⁷. This is the Hilbert–Schmidt sum for the diagonal inverse."),
            Entry("infrared-density", "irDensity", "Frequency-space density",
                "At positive frequency ω use the squared complex norm of the profile divided by ω.",
                DescribeRole.Definition),
            Entry("infrared-divergence", "nonzero_memory_ir_diverges", "Infrared divergence at nonzero memory",
                "For a continuous profile with nonzero value at zero and any positive upper cutoff Λ, "
                + "there are a positive constant a and 0 < δ ≤ Λ such that the integral from ε to Λ "
                + "is at least a log(δ/ε) when 0 < ε < δ. Continuity gives a positive lower bound on "
                + "the squared norm near zero. The cutoff integrals tend to positive infinity as ε "
                + "decreases to zero, and the density is nonintegrable on (0, Λ)."),
            Entry("infrared-integrability", "zero_memory_ir_integrable", "Hölder vanishing makes the density integrable",
                "For a profile continuous on [0, Λ] with Λ > 0, a bound by Cωᵅ in norm on (0, Λ), "
                + "with α > 0, gives an integrable majorant C²ω^(2α − 1)."),
            Entry("dyadic-weight", "dyadic_memory_bin_weight", "Exact dyadic weight",
                "The integral of the reciprocal frequency from 2^(−k−1) to 2^(−k) is log 2 for each natural-number k."),
            Entry("dyadic-profile", "dyadicMemoryProfile", "Dyadic memory profile",
                "Assign the same coefficient m√(log 2) to every dyadic frequency bin for a real parameter m.",
                DescribeRole.Definition),
            Entry("dyadic-nonsummability", "dyadic_memory_not_summable_sq", "Nonzero memory has infinite squared norm",
                "A nonzero parameter gives the same positive squared norm on every bin and hence a divergent sum."),
            Entry("dyadic-difference", "dyadic_memory_diff_summable_sq_iff", "Exact equivalence for two dyadic profiles",
                "The squared norms of the pointwise difference are summable exactly when the two "
                + "real parameters agree."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(NullLocal, NullCone),
            Blocks(Paragraph(Text(statement))), role);
}
