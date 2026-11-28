using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class SchwarzschildOpticalGeodesics4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Observer/carroll1997generalrelativity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Schwarzschild effective potentials yield the photon sphere, critical impact parameter, marginally stable circular orbit and first-order deflection.",
        H("Schwarzschild optical and timelike orbits"),
        Blocks(
            Paragraph(Text("In geometric units, the null potential has its unique positive-radius maximum at three times the mass. The circular timelike family changes stability at six times the mass. Static clock ratios use the Schwarzschild lapse, and the angular endpoint calculation gives the first-order bending angle for weak fields.")),
            Entry("null-potential", "nullPotential", "Null effective potential",
                "Divide the Schwarzschild lapse squared by the areal radius squared.", DescribeRole.Definition, Source),
            Entry("null-potential-has-deriv-at", "nullPotential_hasDerivAt", "Radial derivative",
                "At any nonzero radius the derivative is twice the difference between three masses and the radius, divided by the radius to the fourth power.", DescribeRole.Theorem),
            Entry("photon-sphere-unique", "photon_sphere_unique", "Unique positive stationary radius",
                "The null potential derivative at a positive radius vanishes exactly at three times the mass.", DescribeRole.Theorem),
            Entry("photon-sphere-strict-global-max", "photon_sphere_strict_global_max", "Global maximum of the null potential",
                "For positive mass and radius the potential is at most 1/(27 M²), with equality exactly at r = 3M. The gap factors as a positive factor times (r − 3M)².", DescribeRole.Theorem),
            Entry("photon-sphere-unstable", "photon_sphere_unstable", "Negative radial curvature",
                "At three times the mass the second derivative is minus two divided by eighty-one times the fourth power of the mass.", DescribeRole.Theorem),
            Entry("shadow-critical-impact-eq", "shadow_critical_impact_eq", "Critical impact parameter",
                "The inverse maximum is twenty-seven times the squared mass. Its square root is three times the square root of three times the mass.", DescribeRole.Theorem),
            Entry("shadow-capture-iff", "shadow_capture_iff", "Null capture threshold",
                "For positive impact parameter the inverse squared impact parameter exceeds the potential maximum exactly below the critical impact parameter.", DescribeRole.Theorem),
            Entry("time-potential", "timePotential", "Timelike effective potential",
                "Multiply one half of the lapse squared by one plus the squared angular momentum divided by the squared radius.", DescribeRole.Definition, Source),
            Entry("time-potential-has-deriv-at", "timePotential_hasDerivAt", "Timelike radial derivative",
                "At any nonzero radius the derivative numerator is the mass times the squared radius minus the squared angular momentum times the difference between radius and three masses. The denominator is the fourth power of the radius.", DescribeRole.Theorem),
            Entry("circular-orbit-ang-mom-iff", "circular_orbit_angMom_iff", "Circular angular momentum",
                "For positive mass and r > 3M, the potential derivative vanishes exactly when L² = M r²/(r − 3M).", DescribeRole.Theorem),
            Entry("no-circular-orbit-le-three-m", "no_circular_orbit_le_threeM", "Inner exclusion",
                "For positive mass there is no stationary timelike potential at a positive radius at or below three times the mass.", DescribeRole.Theorem),
            Entry("circular-orbit-second-deriv", "circular_orbit_second_deriv", "Circular radial curvature",
                "At fixed circular-orbit angular momentum, the second derivative is the mass times the difference from six masses divided by the cubed radius and the difference from three masses.", DescribeRole.Theorem),
            Entry("circular-orbit-stability-iff", "circular_orbit_stability_iff", "Stability and marginal radius",
                "The second derivative is positive above six masses, zero there and negative below it on the circular timelike family.", DescribeRole.Theorem),
            Entry("isco-parameters-exact", "isco_parameters_exact", "Parameters at the marginal orbit",
                "The squared angular momentum is twelve times the squared mass and the squared energy is eight ninths. The binding efficiency is one minus two times the square root of two divided by three.", DescribeRole.Theorem),
            Entry("circular-orbit-energy-minimum", "circular_orbit_energy_minimum", "Minimum circular energy",
                "The squared specific energy is minimized exactly at six times the mass. The energy deficit from a particle at rest at infinity is maximal there.", DescribeRole.Theorem),
            Entry("redshift-ratio", "redshiftRatio", "Static clock ratio",
                "Divide the two squared lapses and take the nonnegative square root.", DescribeRole.Definition, Source),
            Entry("schwarzschild-redshift-factor", "schwarzschild_redshift_factor", "Ordered clock rates",
                "For positive mass the clock at the smaller exterior radius has a positive rate strictly below that of the outer clock.", DescribeRole.Theorem, Source),
            Entry("schwarzschild-redshift-horizon-limit", "schwarzschild_redshift_horizon_limit", "Horizon limit",
                "As the inner radius tends to the horizon from above the rate ratio to a fixed exterior clock tends to zero.", DescribeRole.Theorem),
            Entry("u0", "u0", "Unperturbed inverse radius",
                "The leading inverse-radius profile is the sine of the polar angle divided by the impact parameter.", DescribeRole.Definition, Source),
            Entry("u1", "u1", "First-order inverse-radius correction",
                "The correction is the mass divided by squared impact parameter times one plus the squared cosine of the polar angle.", DescribeRole.Definition, Source),
            Entry("binet-zeroth-order-ode", "binet_zeroth_order_ode", "Zeroth-order Binet equation",
                "The second angular derivative plus the profile vanishes at every angle.", DescribeRole.Theorem),
            Entry("binet-first-order-ode", "binet_first_order_ode", "First-order Binet equation",
                "The second angular derivative of the correction plus the correction equals three times the mass times the squared zeroth-order profile.", DescribeRole.Theorem),
            Entry("einstein-light-deflection-eq", "einstein_light_deflection_eq", "First-order light deflection",
                "The difference of the linearized endpoint shifts at zero and pi is four times the mass divided by impact parameter.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role, LibraryNoteRef? source = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(),
            source is null ? AssessedProvenance.FromRepo() : AssessedProvenance.FromRepo(source),
            Blocks(Paragraph(Text(statement))), role);
}
