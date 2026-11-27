using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class NullDiamondDimensionThresholdDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The leading angular model for null diamonds is summable in spacetime dimensions four and five.",
        H("Dimension thresholds for null-diamond angular modes"),
        Blocks(
            Paragraph(Text("The angular model isolates the multiplicity and leading eigenvalue used "
                + "in comparing characteristic covariances in the trace criterion of Satishchandran and Sorce.")),
            Entry("harmonic-multiplicity", "harmonicMult", "Harmonic multiplicity",
                "Take the difference of the homogeneous polynomial dimension in degree ℓ and its "
                + "counterpart in degree ℓ minus two. The second term vanishes for degrees zero and one.",
                DescribeRole.Definition),
            Entry("multiplicity-four", "harmonicMult_four", "Multiplicity in four dimensions",
                "In dimension four the multiplicity is 2ℓ + 1."),
            Entry("multiplicity-five", "harmonicMult_five", "Multiplicity in five dimensions",
                "In dimension five the multiplicity is (ℓ + 1)²."),
            Entry("multiplicity-six", "harmonicMult_six", "Multiplicity in six dimensions",
                "In dimension six the multiplicity is (ℓ + 1)(ℓ + 2)(2ℓ + 3)/6. "
                + "The proof gives the factor of six before taking the natural-number quotient."),
            Entry("multiplicity-growth", "harmonicMult_bounds", "Uniform multiplicity bounds",
                "In each dimension D ≥ 4 the multiplicity lies between positive multiples of ℓ^(D − 3) "
                + "for every ℓ ≥ 1. Two applications of Pascal's identity express the difference "
                + "as a sum of two binomial coefficients of lower degree."),
            Entry("leading-weight", "leadingModeWeight", "Leading angular mode weight",
                "Divide the multiplicity by the square of (ℓ + κ − 1)(ℓ + κ), with κ = (D − 2)/2. "
                + "The weight omits the common amplitude.", DescribeRole.Definition),
            Entry("mode-summability", "leadingModeWeight_summable_iff", "Exact summability window",
                "With the degree-zero term set to zero, the weight is summable exactly in dimensions four "
                + "and five among D ≥ 4. The denominator has growth ℓ⁴. Apply the angular comparison "
                + "theorem to the shifted sequence of positive degrees."),
            Entry("six-dimensional-cutoff", "leadingModeWeight_sum_six_bounds", "Logarithmic cutoff",
                "In dimension six the sum through degree L lies between positive multiples of log L "
                + "for all L ≥ 2. The two bounds follow by comparison with the harmonic sum."),
            Entry("higher-dimensional-cutoff", "leadingModeWeight_sum_ge_seven_bounds", "Power-law cutoff",
                "For D ≥ 7 the sum through degree L lies between positive multiples of L^(D − 6) "
                + "for all L ≥ 1. Compare the lower sum with the integral of the increasing "
                + "power and bound every summand above by its value at the cutoff."),
            Entry("angular-power-integrability", "angular_power_sq_integrable_iff", "Angular power singularity",
                "For D ≥ 5 the product of the weight t^((D − 4)/2) and the square of "
                + "t^(-(D − 4)/2) is integrable on (0, 2] exactly in dimension five. "
                + "On positive t the combined exponent is −(D − 4)/2, which must be greater than −1."),
            Entry("angular-density", "angularSquaredDensity", "Squared angular density",
                "Use the squared logarithm in dimension four and the weighted squared power in higher "
                + "dimensions, in the variable t measured from angular coincidence.", DescribeRole.Definition),
            Entry("angular-density-integrability", "angularSquaredDensity_integrable_iff", "Angular integrability window",
                "The squared angular density is integrable on (0, 2] exactly in dimensions four and five "
                + "among D ≥ 4. The four-dimensional case uses the logarithmic square integral."),
            Entry("conformal-coupling", "deSitterConformalCoupling", "Conformal curvature coupling",
                "The conformal coupling is (D − 2)/(4(D − 1)).", DescribeRole.Definition),
            Entry("scalar-curvature", "deSitterRicciScalar", "De Sitter scalar curvature",
                "For Hubble parameter H the scalar curvature is D(D − 1)H².", DescribeRole.Definition),
            Entry("effective-mass", "deSitterConformalMassSq", "Squared mass relative to the conformal reference",
                "Add the squared mass to the scalar curvature times the displacement of the curvature "
                + "coupling from its conformal value.", DescribeRole.Definition),
            Entry("conformal-subtraction", "deSitterConformalMassSq_eq_sub", "Equivalent conformal subtraction",
                "For D ≥ 4 the relative squared mass is the bare squared mass plus the coupling times "
                + "the scalar curvature, minus κ(κ + 1)H²."),
            Entry("massless-conformal", "deSitterConformalMassSq_conformal", "Massless conformal cancellation",
                "At zero mass and conformal coupling the relative squared mass vanishes."),
            Entry("minimal-massless", "deSitterConformalMassSq_minimal_neg", "Massless minimal coupling",
                "For D ≥ 4 and H > 0 the massless minimally coupled relative squared mass is strictly negative. "
                + "It equals −κ(κ + 1)H²."),
            Entry("de-sitter-mode-summability", "deSitter_leadingModeWeight_summable_iff", "De Sitter leading mode sum",
                "The sum with the squared relative mass coefficient converges exactly when that coefficient "
                + "vanishes or the dimension is four or five. This conclusion concerns the leading angular sum."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
