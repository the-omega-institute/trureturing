using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class BlackHoleThermodynamics4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Observer/christodoulouruffini1971chargedblackhole");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kerr-Newman horizon mechanics, rotational extraction, and Schwarzschild heat capacity.",
        H("Four-dimensional black hole thermodynamics"),
        Blocks(
            Paragraph(Text("Use geometric units for the Kerr-Newman family with zero magnetic charge. "
                + "The mass is positive and the sum of squared electric charge and squared spin parameter is at most the squared mass. "
                + "The Schwarzschild temperature formula restores Newton's constant explicitly.")),
            Entry("spin", "spin", "Spin parameter", "Divide angular momentum by mass.", DescribeRole.Definition),
            Entry("gap", "horizonGap", "Half the horizon separation", "Take the square root of the difference between squared mass and the sum of squared charge and squared spin parameter.", DescribeRole.Definition),
            Entry("outer-radius", "rPlus", "Outer radius", "Add the gap to the mass.", DescribeRole.Definition),
            Entry("inner-radius", "rMinus", "Inner radius", "Subtract the gap from the mass.", DescribeRole.Definition),
            Entry("horizon-factor", "horizonFactor", "Horizon metric factor", "Sum the squares of the outer radius and spin parameter.", DescribeRole.Definition),
            Entry("area", "horizonArea", "Area", "Multiply the horizon metric factor by four pi.", DescribeRole.Definition),
            Entry("gravity", "surfaceGravity", "Surface gravity", "Divide the horizon separation by twice the horizon metric factor.", DescribeRole.Definition),
            Entry("velocity", "angularVelocity", "Angular velocity", "Divide the spin parameter by the horizon metric factor.", DescribeRole.Definition),
            Entry("potential", "electricPotential", "Electric potential", "Multiply the electric charge by the outer radius and divide by the horizon metric factor.", DescribeRole.Definition),
            Entry("irreducible", "irreducibleMass", "Irreducible mass", "Take the square root of the horizon area divided by sixteen pi.", DescribeRole.Definition),
            Entry("positive-area", "horizonArea_pos", "Positive horizon area", "Positive mass makes the outer radius positive, so the metric factor and area are strictly positive."),
            Entry("positive-gravity", "surfaceGravity_pos_of_subextremal", "Subextremal surface gravity", "Positive mass and strictly positive discriminant imply strictly positive surface gravity."),
            Entry("zero-gravity", "surfaceGravity_zero_of_extremal", "Extremal surface gravity", "At equality of squared mass and the sum of squared charge and squared spin parameter, the gap and surface gravity vanish."),
            Entry("horizon-equation", "rPlus_sq_add_a_sq_eq", "Horizon equation", "The metric factor equals twice the product of mass and outer radius minus squared charge for every nonnegative discriminant."),
            Entry("mass-squared", "kerrNewmanMassSq", "Squared thermodynamic mass", "Sum area divided by sixteen pi, half the squared charge, and pi times the sum of fourth power of charge and four times squared angular momentum divided by area.", DescribeRole.Definition),
            Entry("mass", "kerrNewmanMass", "Thermodynamic mass", "Take the square root of the squared thermodynamic mass.", DescribeRole.Definition),
            Entry("irreducible-form", "kerrNewmanMassSq_irreducible", "Irreducible mass form", "For positive area, with irreducible mass m, the squared thermodynamic mass equals the square of m plus charge squared divided by four m, plus angular momentum squared divided by four m squared."),
            Entry("christodoulou-ruffini", "christodoulou_ruffini_mass_sq", "Christodoulou-Ruffini identity", "For positive mass and nonnegative discriminant, the rational squared mass evaluated at the horizon area equals the original squared mass. The horizon equation and the angular momentum relation give the corresponding denominator-cleared identity."),
            Entry("mass-identification", "kerrNewmanMass_eq", "Mass identification", "Under the same conditions, positivity of the original mass identifies it with the square root of the rational squared mass."),
            Entry("first-law", "kerrNewman_first_law", "First law along curves", "For differentiable area, angular momentum, and charge curves through the thermodynamic coordinates of a positive-mass Kerr-Newman solution with nonnegative discriminant, the mass derivative is the sum of surface gravity times area derivative divided by eight pi, angular velocity times angular momentum derivative, and electric potential times charge derivative. The quotient rule and square root derivative give these coefficients using the horizon equation."),
            Entry("partial-area", "kerrNewman_partial_A", "Area derivative", "The mass derivative in area at fixed angular momentum and charge is surface gravity divided by eight pi."),
            Entry("partial-angular-momentum", "kerrNewman_partial_J", "Angular momentum derivative", "The mass derivative in angular momentum at fixed area and charge is the horizon angular velocity."),
            Entry("partial-charge", "kerrNewman_partial_Q", "Charge derivative", "The mass derivative in charge at fixed area and angular momentum is the horizon electric potential."),
            Entry("smarr", "kerrNewman_smarr_formula", "Smarr relation", "For positive mass and nonnegative discriminant the mass equals surface gravity times area divided by four pi, plus twice angular velocity times angular momentum, plus electric potential times charge."),
            Entry("irreducible-bounds", "kerr_irreducible_mass_bounds", "Kerr irreducible mass bounds", "At zero charge, positive mass and absolute angular momentum at most squared mass imply that the irreducible mass lies between mass divided by square root of two and mass."),
            Entry("irreducible-minimum", "kerr_irreducible_mass_min_iff", "Sharp lower irreducible mass", "Equality with mass divided by square root of two holds exactly when absolute angular momentum equals squared mass."),
            Entry("penrose-bound", "penrose_efficiency_bound", "Rotational extraction efficiency", "For two Kerr endpoints with positive masses, admissible angular momenta, and nondecreasing horizon area, the fractional mass decrease is at most one minus the reciprocal of square root of two."),
            Entry("penrose-sharp", "penrose_efficiency_sharp", "Sharp extraction efficiency", "An extremal Kerr endpoint and a Schwarzschild endpoint of equal area attain the stated fractional mass decrease."),
            Entry("hawking-temperature", "hawkingTemp", "Hawking temperature", "Multiply the surface gravity by reduced Planck constant and divide by two pi.", DescribeRole.Definition),
            Entry("entropy", "bekensteinEntropy", "Bekenstein entropy", "Divide area by four times Newton's constant times reduced Planck constant.", DescribeRole.Definition),
            Entry("entropy-differential", "hawking_entropy_differential", "Temperature-entropy differential", "For positive Newton and reduced Planck constants, the product of temperature, entropy derivative in area, and area variation equals surface gravity times area variation divided by eight pi times Newton's constant."),
            Entry("schwarzschild-temperature", "schwarzschildTemp", "Schwarzschild temperature", "Divide reduced Planck constant by eight pi times Newton's constant times mass.", DescribeRole.Definition),
            Entry("schwarzschild-value", "hawking_temp_schwarzschild", "Schwarzschild specialization", "For positive mass and Newton's constant, the horizon temperature of the nonrotating uncharged solution with geometric mass equal to Newton's constant times mass equals the Schwarzschild temperature."),
            Entry("schwarzschild-derivative", "hawking_temp_schwarzschild_deriv", "Schwarzschild temperature derivative", "For positive mass and constants, the derivative is negative reduced Planck constant divided by eight pi times Newton's constant times squared mass, and is strictly negative."),
            Entry("schwarzschild-inverse-temperature", "schwarzschildMassAtTemp", "Mass as a function of temperature", "Divide reduced Planck constant by eight pi times Newton's constant times temperature.", DescribeRole.Definition),
            Entry("heat-capacity", "schwarzschild_specific_heat_neg", "Schwarzschild heat capacity", "For positive mass and constants, the reciprocal-temperature mass branch inverts the Schwarzschild temperature at that mass. Its derivative there equals negative eight pi times Newton's constant times squared mass divided by reduced Planck constant, and is strictly negative."),
            Entry("extremal-limit", "extremal_surface_gravity_tendsto_zero", "Extremal limit", "At fixed positive mass, convergence of the sum of squared electric charge and squared spin parameter to squared mass implies convergence of surface gravity to zero. The nonnegative horizon gap tends to zero and the denominator stays above squared mass."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
