using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class NullModularKMSUniquenessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.";
    private static readonly LibraryNoteRef NullLocal =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");
    private static readonly LibraryNoteRef NullCone =
        LibraryNoteRef.Create("D5/L/HilbertOperators/chandrasekaran2026nullcone");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Detailed balance determines the occupation multiplier. Its complementary symbol gives a bounded continuous strip correlator with an analytic interior, and the affine unitary transports null cuts by dilation.",
        H("Modular detailed balance and null-ray dynamics"),
        Blocks(
            Paragraph(Text("The spectral calculation takes place on the Lebesgue frequency line. The positive thermal occupation is normalized using the reflected symbol from the null-diamond multiplier construction. The affine unitary gives the separate position-space action on the future half-line.")),
            Entry("thermal", "thermal", "Normalized occupation",
                "The inverse temperature β and frequency ν give the multiplier (1 + exp(−βν))⁻¹.", DescribeRole.Definition),
            Entry("detailed-balance", "DetailedBalance", "Covariance detailed balance",
                "The real covariance a and its skew part j satisfy a − j = exp(−βν)(a + j).", DescribeRole.Definition),
            Entry("kms-detailed-balance-unique", "kms_detailed_balance_unique", "Detailed-balance uniqueness",
                "For positive inverse temperature and nonzero frequency, the real detailed-balance equation has one solution for each skew symbol. The ratio of one plus the exponential to one minus the exponential equals the hyperbolic cotangent at half the scaled frequency."),
            Entry("kms-normalized-symbol-unique", "kms_normalized_symbol_unique", "Normalized symbol uniqueness",
                "Solving the occupation balance equation yields the logistic multiplier and every such multiplier solves the equation."),
            Entry("kms-normalized-symbol-properties", "kms_normalized_symbol_properties", "Occupation and reflection identities",
                "The logistic multiplier is strictly between zero and one at every real frequency. Reflection exchanges the occupation and its complement, and twice the occupation minus one equals the hyperbolic tangent of half the scaled frequency. Adding or subtracting that tangent from one yields twice the positive or reflected occupation respectively."),
            Entry("kms-beta-two-pi-equals-null-a", "kms_beta_two_pi_equals_nullA", "Normalization of the null-cone multiplier",
                "The multiplier convention uses the reflected frequency and half the existing null-cone symbol. Scaling frequency by twice pi gives the inverse-temperature convention of modular time."),
            Entry("phase", "phase", "Complex frequency phase",
                "The complex time z and real frequency ν give exp(−izν).", DescribeRole.Definition),
            Entry("strip-kernel", "stripKernel", "Complex strip kernel",
                "Multiply the complex frequency phase by (1 + exp(βν))⁻¹.", DescribeRole.Definition),
            Entry("kms-strip", "kmsStrip", "Complex strip correlation",
                "Integrate the product of the complex spectral density and the strip kernel over the real frequency line.", DescribeRole.Definition),
            Entry("modular-kms-strip-integrable", "modular_kms_strip_integrable", "Closed-strip integrability",
                "The spectral multiplier with denominator one plus exp(βν) and phase exp(−izν) has absolute value at most one for imaginary part between zero and β. Thus every complex integrable spectral density gives an integrable kernel throughout the closed strip."),
            Entry("modular-kms-strip-bounded", "modular_kms_strip_bounded", "Uniform closed-strip bound",
                "The absolute value of the correlation is at most the integral of the absolute value of the density on the whole closed strip."),
            Entry("modular-kms-strip-continuous", "modular_kms_strip_continuous", "Continuity on the closed strip",
                "Dominated convergence with the integrable norm of the density gives continuity, including at the two boundary lines."),
            Entry("modular-kms-strip-holomorphic", "modular_kms_strip_holomorphic", "Holomorphy in the open strip",
                "At each interior point there is a neighborhood separated from both boundaries by a positive distance. The derivative multiplier is bounded by |ν| exp(−δ|ν|) on that neighborhood, which gives an integrable dominating function and permits differentiation under the integral."),
            Entry("modular-kms-lower-boundary", "modular_kms_lower_boundary", "Lower boundary",
                "At real modular time the strip kernel is the complementary thermal occupation times the real-time phase."),
            Entry("modular-kms-upper-boundary", "modular_kms_upper_boundary", "Upper boundary",
                "At imaginary displacement β the phase acquires the factor exp(βν). This transforms the complementary occupation into the thermal occupation, with the real-time phase preserved."),
            Entry("thermal-op", "thermalOp", "Thermal multiplication operator",
                "On the Lebesgue Hilbert space of square-integrable complex functions, multiply by the normalized occupation.", DescribeRole.Definition),
            Entry("spectral-flow", "spectralFlow", "Real-time spectral multiplication",
                "On the same frequency Hilbert space multiply by the complex exponential phase at real time.", DescribeRole.Definition),
            Entry("modular-kms-boundary-identities", "modular_kms_boundary_identities", "Hilbert-space boundary identities",
                "The product of the conjugate of the first square-integrable vector and the second square-integrable vector is integrable by Hölder's inequality. The two boundary formulas become the corresponding inner products with the bounded spectral multipliers acting on the second vector."),
            Entry("kms-strip-determines-temperature", "kms_strip_determines_temperature", "Uniqueness of inverse temperature",
                "For a nonnegative integrable spectral density supported on positive frequencies and having strictly positive total mass, the upper boundary at zero real time is strictly increasing with inverse temperature. Equality of two upper boundary values forces equality of the inverse temperatures."),
            Entry("boost-ray", "boostRay", "Geometric coordinate dilation",
                "The modular coordinate pullback sends x to exp(2πs)x.", DescribeRole.Definition),
            Entry("hsmi-modular-boost-preserves-halfline", "hsmi_modular_boost_preserves_halfline", "Future half-line invariance",
                "The existing affine unitary acts almost everywhere by a positive coordinate dilation and a strictly positive scalar normalization. A vector supported on the positive half-line remains supported there."),
            Entry("hsmi-modular-boost-ray-map", "hsmi_modular_boost_ray_map", "Geometric boost and transported cuts",
                "The dilation fixes the horizon at zero, composes by addition of modular times, and pulls the cut at a back to the cut at exp(−2πs)a. It preserves the positive half-line."),
            Entry("hsmi-modular-boost-cut", "hsmi_modular_boost_cut", "Transport of cut-supported vectors",
                "A square-integrable vector vanishes almost everywhere below a exactly when its modular evolution vanishes almost everywhere below exp(−2πs)a. The inverse dilation proves the reverse implication."),
            Entry("hsmi-modular-boost-cut-inclusion", "hsmi_modular_boost_cut_inclusion", "Half-sided geometric inclusion",
                "For nonnegative modular time and positive a, the original ray starting at a is contained in its pullback by the dilation. Conjugation of a translation by the inverse modular time action rescales its displacement by exp(2πs)."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(NullLocal, NullCone),
            Blocks(Paragraph(Text(statement))), role);
}
