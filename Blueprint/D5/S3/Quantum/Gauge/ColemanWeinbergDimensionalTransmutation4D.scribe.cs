using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Gauge;

internal sealed class ColemanWeinbergDimensionalTransmutation4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/LieTheory/colemanweinberg1973radiative");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourth-derivative renormalization, dimensional transmutation, and stability for a one-loop scalar potential.",
        H("Coleman–Weinberg dimensional transmutation in four dimensions"),
        Blocks(
            Paragraph(Text("A logarithmic quartic correction to the massless scalar potential selects a positive field scale. The same correction fixes the curvature at the minima and determines whether the potential is bounded below. The scale invariance here refers to changing the renormalization point while running the quartic at fixed logarithmic coefficient.")),
            Entry("gauge-coefficient", "cwCoeff", "Scalar electrodynamics coefficient",
                "The logarithmic coefficient is three times the fourth power of the electric coupling divided by sixty-four times pi squared.", DescribeRole.Definition),
            Entry("renormalized-potential", "cwPotential", "Renormalized one-loop potential",
                "The classical coefficient is the quartic coupling divided by twenty-four. The correction is the logarithmic coefficient times the fourth power of the field times the logarithm of the squared field-to-scale ratio minus twenty-five sixths.", DescribeRole.Definition),
            Entry("universal-potential", "cwUniversal", "Potential expressed at its vacuum scale",
                "Multiply the logarithmic coefficient and the fourth power of the field by the logarithm of the squared field-to-vacuum ratio minus one half.", DescribeRole.Definition),
            Entry("vacuum-scale", "cwVev", "Transmuted scale",
                "Multiply the renormalization scale by the exponential of eleven sixths minus the quartic coupling divided by forty-eight times the logarithmic coefficient.", DescribeRole.Definition),
            Entry("running-quartic", "cwRunningLam", "Running quartic at fixed logarithmic coefficient",
                "Add forty-eight times the logarithmic coefficient times the logarithm of the scale-to-reference ratio to the reference quartic.", DescribeRole.Definition),
            Entry("gauge-yukawa-coefficient", "cwEffCoeff", "Gauge and Yukawa coefficient",
                "Subtract four times the color multiplicity times the fourth power of the Yukawa coupling from three times the fourth power of the gauge coupling, then divide by sixty-four times pi squared.", DescribeRole.Definition),
            Entry("fourth-derivative", "cw_fourth_derivative_renormalization_condition", "Fourth-derivative renormalization",
                "At a positive renormalization field, the fourth derivative of the logarithmic quartic is one hundred and that of its subtracted form is zero. The full fourth derivative is the prescribed quartic coupling. For a nonzero correction coefficient, a constant subtraction has this property exactly when it is twenty-five sixths."),
            Entry("coupling-lock", "cw_dimensional_transmutation_and_coupling_lock", "Dimensional transmutation and the quartic coupling",
                "For positive logarithmic coefficient and renormalization scale, the transmuted scale is positive. The two potential expressions agree at every real field and the potential is continuous at zero. The renormalization scale is the vacuum scale exactly when the quartic equals eighty-eight times the logarithmic coefficient, which in scalar electrodynamics is thirty-three times the fourth power of the gauge coupling divided by eight pi squared."),
            Entry("global-minimum", "cw_radiative_global_minimum_and_symmetry_breaking", "Two global minima",
                "For positive coefficient and vacuum scale the derivative is four times the coefficient, the cubed field, and the logarithm of the squared field-to-vacuum ratio, including derivative zero at the origin. The global minimum on the real line is attained exactly at the two signed vacuum fields. Its value is minus half the coefficient times the fourth power of the vacuum scale and lies strictly below the value zero at the origin."),
            Entry("mass-ratio", "cw_radiative_scalar_to_vector_mass_ratio", "Curvature and mass ratio",
                "For positive logarithmic coefficient, vacuum scale, and electric coupling, the derivative of the potential derivative at the vacuum is eight times the coefficient and the squared vacuum scale, which is positive. The charged mass formula of the Higgs module evaluated at twice the scalar-electrodynamics coupling gives the squared vector mass. At the scalar-electrodynamics coefficient, the squared mass ratio is three times the squared electric coupling divided by eight pi squared, equivalently three times the fine-structure constant divided by twice pi."),
            Entry("callan-symanzik", "cw_callan_symanzik_rg_invariance", "Exact invariance under quartic running",
                "For positive coefficient and scales, the scale times the derivative of the running quartic is forty-eight times the coefficient, reducing to nine times the fourth power of the electric coupling divided by four pi squared in scalar electrodynamics. Substituting the running quartic preserves the transmuted scale and the potential at every real field."),
            Entry("yukawa-threshold", "cw_yukawa_vacuum_stability_threshold", "Strict gauge–Yukawa threshold",
                "The effective coefficient is positive exactly when four times the color multiplicity times the fourth power of the Yukawa coupling is less than three times the fourth power of the gauge coupling. At a positive renormalization scale, a positive coefficient gives a bounded-below potential tending to positive infinity with the field, and a negative coefficient gives a potential tending to negative infinity."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
