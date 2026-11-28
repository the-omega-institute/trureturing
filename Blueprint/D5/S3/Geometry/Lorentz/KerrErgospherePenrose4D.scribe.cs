using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class KerrErgospherePenrose4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Observer/bardeenpressteukolsky1972kerr");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stationary limits, horizon rotation, extraction, and equatorial Kerr orbits.",
        H("Kerr ergosphere and equatorial orbits"),
        Blocks(
            Paragraph(Text("The Kerr horizon is a root of the radial polynomial. The outer stationary limit instead comes from the time component of the metric. Between these two surfaces every stationary timelike observer rotates with the black hole.")),
            Entry("radial-polynomial", "kerrDelta", "Radial polynomial",
                "Add the squared radius and squared spin and subtract twice the mass times the radius.", DescribeRole.Definition),
            Entry("latitude-factor", "kerrSigma", "Latitude factor",
                "Add the squared radius and squared spin times squared cosine of the polar angle.", DescribeRole.Definition),
            Entry("azimuth-factor", "kerrA", "Azimuthal metric factor",
                "Subtract the radial polynomial times squared spin and squared sine from the square of the sum of squared radius and squared spin.", DescribeRole.Definition),
            Entry("stationary-determinant", "kerr_metric_2d_det", "Time and azimuth determinant",
                "When the latitude factor is nonzero, the determinant equals minus the radial polynomial times squared sine."),
            Entry("horizon-roots", "kerrDelta_factorization", "Horizon factorization",
                "The radial polynomial factors into the differences from the outer and inner horizon radii when the absolute spin is at most the mass."),
            Entry("stationary-limit", "ergosphere_strictly_outside_horizon", "Separation from the horizon",
                "The stationary limit lies at or above the outer horizon. For nonzero spin the separation is strict exactly where the sine of the polar angle is nonzero."),
            Entry("time-spacelike", "g_tt_positive_in_ergosphere", "Spacelike time translation",
                "For positive mass between the outer horizon and stationary limit, the norm squared of the time-translation Killing vector is positive."),
            Entry("rigid-rotation", "frameDrag_at_horizon_rigid", "Horizon angular velocity",
                "Away from the axis the frame angular velocity at the outer horizon equals the spin divided by twice the product of mass and horizon radius."),
            Entry("angular-window", "timelike_omega_window_iff", "Open timelike angular interval",
                "Outside the horizon and away from the axis the circular norm factors into the azimuthal coefficient and the two differences from the null angular velocities. The norm is negative exactly between those velocities."),
            Entry("lorentz-signature", "kerr_exterior_metric_signature", "Exterior metric signature",
                "Completing the time and azimuth square gives one negative and three positive diagonal coefficients outside the outer horizon and away from the axis."),
            Entry("corotation", "ergosphere_forbids_static_observer", "Mandatory co-rotation",
                "For positive spin in the ergoregion, the lower null angular velocity is positive, the static circular vector is spacelike, and every timelike circular vector has positive angular velocity."),
            Entry("negative-energy", "penrose_extraction_forces_retrograde", "Penrose energy gain",
                "The future horizon inequality forces the captured particle's angular momentum to be negative when its Killing energy is negative. Energy conservation in the split then bounds the escaping energy strictly above the incoming energy."),
            Entry("area-law", "penrose_area_nondecrease_iff", "Area and irreducible mass",
                "For neutral subextremal Kerr along differentiable thermodynamic curves, the area derivative, the irreducible-mass derivative, and the mass derivative minus horizon angular velocity times angular momentum derivative have the same nonnegative sign."),
            Entry("superradiant-threshold", "superradiance_condition_iff", "Superradiance threshold",
                "With positive frequency and flux coefficient the horizon energy flux is negative exactly when the frequency is less than the azimuthal number times the angular velocity of the horizon."),
            Entry("photon-radii", "kerr_photon_orbit_benchmarks", "Photon radii",
                "For positive radius the nonrotating polynomial vanishes at the stationary radius of the Schwarzschild null potential. At extremal spin the polynomial has a double root at one mass and a simple root at four masses."),
            Entry("photon-directions", "extremal_photon_orbit_directions", "Extremal photon directions",
                "The signed circular-photon equation assigns one mass to the prograde root and four masses to the retrograde root."),
            Entry("isco-unique", "extremal_isco_radii_unique", "Unique positive extremal marginal radii",
                "The signed marginal-stability equations factor in the dimensionless square-root radius, leaving one positive root for each direction."),
            Entry("isco-radii", "kerr_isco_benchmarks_and_binding_efficiency", "Marginal stability and binding efficiency",
                "The nonrotating radius is six masses. The extremal prograde and retrograde radii are one and nine masses. The positive binding efficiencies increase in the order retrograde, Schwarzschild, prograde, and all are below one half."),
            Entry("circular-energy", "isco_efficiency_eq_orbit_binding", "Energy at marginal stability",
                "At a positive marginally stable radius, on the timelike branch with nonnegative specific energy, the circular-orbit energy is the square root of one minus two masses divided by three radii."),
            Entry("extremal-energy", "extremal_prograde_energy_limit", "Extremal prograde energy limit",
                "Factoring the numerator and the square-root argument cancels a common factor on the exterior. As the dimensionless square-root radius tends to one from above, the specific energy tends to the reciprocal of square root of three."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
