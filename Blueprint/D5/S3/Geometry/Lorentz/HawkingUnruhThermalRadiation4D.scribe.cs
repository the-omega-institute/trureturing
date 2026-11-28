using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class HawkingUnruhThermalRadiation4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Observer/gibbonshawking1977euclidean");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Horizon periodicity, thermal moments, and entropy production in a four-dimensional blackbody evaporation model.",
        H("Hawking and Unruh thermal radiation in four dimensions"),
        Blocks(
            Paragraph(Text("The leading Euclidean polar metric fixes the thermal period by the circumference-to-radius test. Detailed balance gives the bosonic and fermionic occupation numbers. In the Schwarzschild blackbody model, the spectral moments set the power scale and the mass-loss and entropy laws determine the complete evaporation trajectory.")),
            Entry("euclidean-circumference", "euclideanCircumference", "Euclidean time orbit length",
                "Integrate the speed of the fixed-radius circular orbit over one Euclidean period.", DescribeRole.Definition),
            Entry("conical-period", "gibbons_hawking_conical_periodicity", "Euclidean period and horizon temperature",
                "For positive surface gravity, Euclidean period, and radius, the circumference divided by twice pi times the radius is the product of gravity and period divided by twice pi. The ratio is one exactly at the period twice pi over surface gravity. Its reciprocal is the Hawking temperature in natural units, with acceleration as the Unruh parameter and inverse eight pi times the mass in Schwarzschild."),
            Entry("thermal-spectra", "bogoliubov_planck_and_fermi_dirac_spectra", "Bose and Fermi detailed balance",
                "For positive inverse temperature and frequency, write E for the exponential of their product and set A equal to E times B. Bosonic normalization fixes A minus B to one, so A equals one plus B and the numerators E and one have denominator E minus one. Fermionic normalization fixes A plus B to one, so A equals one minus B and the same numerators have denominator E plus one. The bosonic occupation is positive. The fermionic occupation lies strictly between zero and one half, and its complement agrees with the modular KMS symbol. Dividing the occupation by one plus B for bosons and by one minus B for fermions gives the reciprocal of E. Frequency times the bosonic occupation tends to the reciprocal inverse temperature at zero from above, and E times that occupation tends to one at infinite frequency."),
            Entry("thermal-moments", "stefan_boltzmann_4d_bose_and_fermi_integrals", "Bose and Fermi cubic moments",
                "The cubic Bose integral on the positive real half-line is pi to the fourth power divided by fifteen. The geometric expansion of the occupation number permits termwise integration of nonnegative functions. The Fermi integral is seven eighths of the Bose integral because subtracting twice the Bose integrand with doubled exponential argument introduces a factor of one sixteenth after rescaling."),
            Entry("bosonic-flux-coefficient", "bosonicStefanBoltzmann", "Flux coefficient for one bosonic helicity",
                "Divide the cubic Bose moment by eight pi squared.", DescribeRole.Definition),
            Entry("hawking-power-law", "hawkingLuminosity", "Blackbody luminosity",
                "Multiply the effective helicity count and the single-helicity flux coefficient by the horizon area and fourth power of the Schwarzschild temperature.", DescribeRole.Definition),
            Entry("inverse-square-luminosity", "hawking_luminosity_inverse_square_law", "Schwarzschild inverse-square luminosity",
                "At positive mass the horizon area times the fourth power of the temperature gives an inverse-square mass law. With the single-helicity thermal coefficient, the result is the effective helicity count divided by thirty thousand seven hundred twenty times pi and the squared mass."),
            Entry("evaporation-time", "evapTime", "Evaporation time",
                "The lifetime is the initial mass cubed divided by three times the evaporation coefficient.", DescribeRole.Definition),
            Entry("evaporating-mass", "evapMass", "Mass along the trajectory",
                "Multiply the initial mass by the cube root of one minus the elapsed fraction of the lifetime.", DescribeRole.Definition),
            Entry("evaporation-trajectory", "hawking_evaporation_trajectory_and_runaway_heating", "Evaporation and increasing temperature",
                "For positive initial mass and evaporation coefficient, the evaporation time is the cubed initial mass divided by three times the coefficient. The mass starts at the initial mass and is positive before the endpoint. Its derivative is minus the evaporation coefficient divided by squared instantaneous mass. At the endpoint the mass tends to zero from the left and the temperature tends to positive infinity."),
            Entry("radiation-entropy-flux", "radiationEntropyFlux", "Radiation entropy flux",
                "The enthalpy flux is the power plus one third of the power. Dividing it by the radiation temperature gives the entropy flux.", DescribeRole.Definition),
            Entry("modeled-hawking-power", "hawkingPower", "Power in the evaporation equation",
                "Divide the evaporation coefficient by the squared instantaneous mass.", DescribeRole.Definition),
            Entry("schwarzschild-entropy", "schwarzschildEntropy", "Schwarzschild horizon entropy",
                "Use the Bekenstein–Hawking formula in natural units with vanishing charge and angular momentum.", DescribeRole.Definition),
            Entry("evaporation-entropy-flux", "evaporationEntropyFlux", "Entropy flux along the evaporation trajectory",
                "Evaluate the radiation entropy flux at the power and temperature of the instantaneous Schwarzschild mass.", DescribeRole.Definition),
            Entry("generalized-entropy", "zurek_generalized_second_law_irreversible_entropy_production", "Exact entropy production",
                "For positive initial mass and evaporation coefficient, from time zero up to the lifetime endpoint, the horizon entropy is four pi times the squared mass. Its derivative is minus the emitted power divided by temperature, equal to minus eight pi times the evaporation coefficient divided by the mass. With pressure one third of the energy density the ideal thermal radiation carries four thirds of the positive power-to-temperature ratio. The generalized rate is one third of this ratio, equal to eight pi times the evaporation coefficient divided by three times the instantaneous mass. The flux is integrable at the endpoint. Its lifetime integral is four thirds of the initial horizon entropy, leaving a positive net increase of one third of the initial horizon entropy."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
