using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class FLRWCosmologyFriedmann4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.";
    private static readonly LibraryNoteRef Carroll =
        LibraryNoteRef.Create("D5/L/Observer/carroll1997generalrelativity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Friedmann conservation, exact fluid and dust-vacuum expansion, and conformal horizons.",
        H("Four-dimensional FLRW cosmology"),
        Blocks(
            Paragraph(Text("The Friedmann equations use cosmological time and a positive scale factor. "
                + "Newton's constant is explicit and the cosmological constant is separate from the fluid density.")),
            Entry("continuity", "friedmann_implies_continuity", "Energy conservation",
                "The first Friedmann equation holds near the time in question and the acceleration equation holds at that time. "
                + "Differentiating the curvature-inclusive first equation and using the acceleration equation leaves the continuity expression multiplied by minus eight pi G times the square of the scale factor divided by three. "
                + "Positive Newton's constant and scale factor permit cancellation."),
            Entry("first-integral", "continuity_and_friedmann_II_conserve_first_integral", "Conserved first integral",
                "The continuity and acceleration equations make the derivative of the squared velocity minus the density and cosmological terms zero."),
            Entry("equation-of-state", "eosDensity", "Constant pressure ratio density",
                "Multiply the reference density by the scale-factor ratio raised to minus three times one plus the pressure ratio.", DescribeRole.Definition),
            Entry("density-derivative", "eosDensity_continuity_ode", "Continuity for a constant pressure ratio",
                "At positive reference and current scale factors, the density derivative is minus three times the product of the Hubble rate, one plus the pressure ratio, and the density."),
            Entry("fluid-scalings", "eosDensity_dust_radiation_vacuum", "Dust, radiation and vacuum",
                "For a nonnegative scale-factor ratio, the dust and radiation densities divide the reference density by the third and fourth powers of the ratio. The vacuum density is constant."),
            Entry("strong-energy", "acceleration_iff_strong_energy_violation", "Fluid acceleration threshold",
                "At zero cosmological constant and positive scale factor, Newton's constant and density, the acceleration is positive exactly when the pressure ratio is below minus one third."),
            Entry("dust-acceleration", "dust_acceleration_iff", "Dust acceleration threshold",
                "At positive scale factor in the dust acceleration equation, the acceleration is positive exactly when the cosmological constant exceeds four pi G times the dust density."),
            Entry("flat-exponent", "flatExponent", "Flat fluid exponent",
                "Divide two by three times one plus the pressure ratio.", DescribeRole.Definition),
            Entry("flat-scale", "flatScaleFactor", "Power-law scale factor",
                "Multiply the indicated power of cosmological time by the normalization.", DescribeRole.Definition),
            Entry("flat-density", "flatDensity", "Power-law density",
                "Take the reciprocal of six pi G times the square of one plus the pressure ratio times squared time.", DescribeRole.Definition),
            Entry("hubble", "hubble", "Hubble rate",
                "Divide the time derivative of the scale factor by the scale factor.", DescribeRole.Definition),
            Entry("deceleration", "deceleration", "Deceleration parameter",
                "Divide minus the product of the scale factor and its second derivative by the squared first derivative.", DescribeRole.Definition),
            Entry("flat-friedmann", "flat_power_law_satisfies_friedmann", "Exact flat fluid solution",
                "For positive time, normalization and Newton's constant and pressure ratio above minus one, the squared Hubble rate is eight pi G times the explicit density divided by three. "
                + "The normalized second derivative is minus four pi G times the density and one plus three times the pressure ratio, divided by three."),
            Entry("hubble-age", "flat_power_law_hubble_age", "Age and Hubble rate",
                "For positive time and scale normalization, the product of the Hubble rate and time is the power-law exponent."),
            Entry("dust-radiation-age", "flat_dust_radiation_age", "Age for dust and radiation",
                "For positive time and scale normalization, the age is two divided by three times the Hubble rate for dust and one divided by twice that rate for radiation."),
            Entry("flat-deceleration", "flat_power_law_deceleration", "Exact constant deceleration parameter",
                "For pressure ratio above minus one and positive time and normalization, the deceleration parameter is half of one plus three times the pressure ratio."),
            Entry("deceleration-thresholds", "flat_deceleration_thresholds", "Deceleration thresholds",
                "The deceleration parameter is one half for dust and one for radiation. For pressure ratio above minus one, it is negative exactly below minus one third."),
            Entry("dust-vacuum-scale", "lcdmScaleFactor", "Dust and vacuum scale factor",
                "Multiply the scale normalization by the two-thirds power of the hyperbolic sine of three halves times the vacuum Hubble rate times time.", DescribeRole.Definition),
            Entry("dust-vacuum-density", "lcdmDensity", "Dust density",
                "Divide the squared vacuum Hubble rate times the cubed ratio of normalization to scale factor by eight pi G divided by three.", DescribeRole.Definition),
            Entry("dust-vacuum-hubble", "lcdm_hubble_eq", "Dust and vacuum Hubble rate",
                "For positive normalization, vacuum Hubble rate and time, the Hubble rate is the vacuum Hubble rate times the hyperbolic cotangent of the scale-factor argument."),
            Entry("dust-vacuum-first", "lcdm_satisfies_friedmann_I", "First flat dust and vacuum equation",
                "For positive normalization, vacuum Hubble rate, Newton's constant and time, the squared Hubble rate is the sum of eight pi G times the dust density divided by three and the squared vacuum Hubble rate."),
            Entry("dust-vacuum-second", "lcdm_satisfies_friedmann_II", "Second flat dust and vacuum equation",
                "Under the same positivity conditions, the normalized second derivative is the squared vacuum Hubble rate minus four pi G times the dust density divided by three."),
            Entry("inflection", "lcdm_inflection_iff", "Acceleration onset",
                "For positive normalization, vacuum Hubble rate and time, acceleration is positive exactly when the hyperbolic sine of the scale-factor argument exceeds the reciprocal square root of two."),
            Entry("density-parameter-acceleration", "lcdm_density_parameter_acceleration", "Density parameter acceleration threshold",
                "For positive normalization, vacuum Hubble rate, Newton's constant and time, acceleration is positive exactly when the matter density parameter is less than twice the vacuum density parameter."),
            Entry("matter-vacuum-ratio", "lcdmMatterVacuumRatio", "Matter-to-vacuum density ratio",
                "Cube the ratio of scale normalization to scale factor.", DescribeRole.Definition),
            Entry("transition-scale", "lcdm_transition_scale", "Transition scale",
                "For positive normalization, vacuum Hubble rate and time, acceleration vanishes exactly when the scale factor divided by its normalization equals two to the power minus one third."),
            Entry("transition-time", "lcdm_transition_time", "Unique positive transition time",
                "Divide the inverse hyperbolic sine of the reciprocal square root of two by three halves times the vacuum Hubble rate. This gives a positive time, and it is the unique positive time at which acceleration vanishes."),
            Entry("transition-redshift", "lcdm_transition_redshift", "Transition redshift",
                "At a positive reference time and a positive time of vanishing acceleration, the cube of the reference-to-transition scale ratio equals twice the reciprocal of the matter-to-vacuum density ratio at the reference time."),
            Entry("future-limit", "lcdm_hubble_tendsto_desitter", "Future Hubble limit",
                "For positive normalization and vacuum Hubble rate, the Hubble rate converges to the vacuum Hubble rate as time tends to positive infinity."),
            Entry("particle-finite", "particle_horizon_finite_iff", "Finite particle horizon",
                "At a positive cutoff time, the inverse power is integrable from the initial singularity exactly when the expansion exponent is below one."),
            Entry("event-finite", "event_horizon_finite_iff", "Finite event horizon",
                "At a positive cutoff time, the inverse power is integrable to infinite future time exactly when the expansion exponent is above one."),
            Entry("particle-value", "particle_horizon_integral", "Particle horizon distance",
                "For expansion exponent below one, the conformal distance is the cutoff raised to one minus the exponent divided by one minus the exponent."),
            Entry("event-value", "event_horizon_integral", "Event horizon distance",
                "For expansion exponent above one, the conformal distance is the cutoff raised to one minus the exponent divided by the exponent minus one."),
            Entry("horizon-fluid-thresholds", "flat_horizon_thresholds", "Horizon thresholds for the pressure ratio",
                "For pressure ratio above minus one and a positive cutoff, the particle horizon is finite exactly above minus one third and the event horizon is finite exactly below minus one third."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Carroll),
            Blocks(Paragraph(Text(statement))), role);
}
