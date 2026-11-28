using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class NullDiamondDeSitterKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The de Sitter cone admits an exact area-weighted flux and a conformal kernel specialization.",
        H("De Sitter null-diamond kernels"),
        Blocks(
            Paragraph(Text("The area-weighted field gives the characteristic flux in the conformal chart. "
                + "The normalized Bunch–Davies differential equation identifies the first local mass term. "
                + "The massless invariant differential equation gives a separate obstruction at the antipode.")),
            Entry("mobius", "dsMobius", "Conformal radial map",
                "Use f(u) = u/(T − u) along a null generator.", DescribeRole.Definition),
            Entry("factor", "dsOmega", "Conformal factor",
                "Use Ω(u) = 1/(H(T − u)) on the expanding chart.", DescribeRole.Definition),
            Entry("affine", "dsAffine", "Affine parameter",
                "Divide the radial map f by H²T to fix the affine normalization.", DescribeRole.Definition),
            Entry("mobius-derivative", "ds_mobius_hasDerivAt", "Derivative of the radial map",
                "For u < T, the derivative is T/(T − u)²."),
            Entry("affine-derivative", "ds_affine_hasDerivAt", "Affine Jacobian",
                "With H and T positive, the affine derivative is Ω(u)²."),
            Entry("flux", "ds_flux_wronskian_eq", "Characteristic Wronskian",
                "With the area radius ρ = uΩ, multiply each scalar profile by ρ raised to κ. "
                + "In the skew pairing, the derivative of this factor cancels. The affine derivative "
                + "cancels its Jacobian and the weight becomes ρ raised to 2κ."),
            Entry("logarithm", "ds_mobius_log_eq", "Logarithm under the radial map",
                "Off the diagonal, the transformed real logarithm of the absolute difference "
                + "is the original logarithm plus log T and the two separate logarithmic corrections."),
            Entry("logarithm-mixed", "ds_mobius_log_mixed_deriv", "Off-diagonal mixed derivative",
                "The correction depending on the second coordinate becomes constant when differentiated "
                + "in that coordinate. The subsequent derivative in the first coordinate removes it."),
            Entry("affine-boundary-logarithm", "ds_affine_boundary_log_ae", "Affine boundary logarithm",
                "The complex logarithms of the two real differences have the same boundary phase. "
                + "Their difference almost everywhere is a real sum of separate radial terms."),
            Entry("weak-mixed-derivative", "ds_affine_boundary_log_mixed_weak",
                "Weak mixed derivative of the affine correction",
                "On each compact radial interval below T, the boundary logarithm difference pairs to zero "
                + "against the product of the derivatives of two continuously differentiable test functions "
                + "that vanish at both endpoints."),
            Entry("chord", "dsChord", "Chord variable",
                "Multiply the two radial map values by y/4, where y denotes the angular separation variable.",
                DescribeRole.Definition),
            Entry("mixed-kernel", "ds_mixed_product_rule", "Area-weighted mixed derivative",
                "The area weights cancel the chord power, leaving the constant H raised to −2κ times "
                + "(4/y) raised to κ. Differentiating the remaining composition gives the radial "
                + "logarithmic derivatives of f times the sum of s²Uʺ and sUʹ."),
            Entry("ode", "bdODE", "Bunch–Davies differential operator",
                "Apply the hypergeometric differential expression to the normalized kernel Y.",
                DescribeRole.Definition),
            Entry("constant-solution", "bdODE_conformal_constant", "Conformal constant solution",
                "At zero relative mass, the normalized Bunch–Davies operator annihilates the constant one."),
            Entry("relative-mass", "bd_conformal_parameter_eq", "Conformal locus",
                "For positive H and D at least four, the mass after subtracting the conformal value "
                + "and dividing by H² vanishes exactly when m² + (ξ − ξc)R vanishes."),
            Entry("formal-ode", "bdFormalODE", "Formal series operator",
                "Replace the derivatives in the Bunch–Davies equation by formal differentiation on "
                + "real power series.", DescribeRole.Definition),
            Entry("frobenius", "bd_frobenius_recurrence", "Frobenius recurrence",
                "Compute each coefficient of the formal differential expression. It vanishes in every "
                + "degree exactly when (j + 1)(j + 1 − κ) times the next coefficient equals "
                + "(j(j + 1) + e) times the current coefficient."),
            Entry("first-coefficient", "bd_first_coefficient", "First mass coefficient",
                "With constant coefficient one and κ different from one, the linear coefficient is e/(1 − κ)."),
            Entry("resonance", "bd_resonance", "Dimension-four analytic obstruction",
                "At κ = 1, the degree-zero recurrence of any normalized formal power series forces e = 0."),
            Entry("log-coefficient", "bd_resonant_log_coefficient", "Dimension-four logarithmic coefficient",
                "For a twice differentiable solution of the dimension-four equation tending to one at the tip, "
                + "the quotient (Y(s) − 1)/(s log s) tends to e. The equation controls the derivative of "
                + "the weighted derivative (1 − s)²Yʹ(s)."),
            Entry("leading-mode", "dsLeadingCoefficient", "Leading angular coefficient",
                "The coefficient in positive harmonic degree is the product of the two radial derivatives "
                + "and −e/(4π), divided by (ℓ + κ − 1)(ℓ + κ).", DescribeRole.Definition),
            Entry("angular-moment-evaluation", "ds_leading_angular_coefficient_eq",
                "Power and logarithmic angular moments",
                "Evaluate the closed angular moment at exponent 1 − κ for κ > 1, and differentiate "
                + "it at exponent zero for κ = 1. Both calculations give the same normalized coefficient "
                + "in positive harmonic degree."),
            Entry("leading-sign", "ds_leading_coefficient_sign", "Sign of the leading mode",
                "For κ at least one and positive harmonic degree, all radial and angular factors are positive. "
                + "The coefficient vanishes at e = 0 and otherwise has sign opposite to eH². "
                + "The result applies to κ = 1 in dimension four and κ = 3/2 in dimension five."),
            Entry("conformal-kernel", "bd_conformal_hypergeometric", "Exact conformal kernel equality",
                "For positive κ and 0 < s < 1, the ordinary hypergeometric series at conformal parameters "
                + "reduces to the binomial series for the power s raised to −κ. Cancelling the common "
                + "Gamma factor yields the conformal kernel with its full normalization."),
            Entry("antipodal", "allen_folacci_antipodal_obstruction", "Massless invariant antipodal obstruction",
                "On −1 < P < 1, multiplication by (1 − P²) raised to D/2 makes the derivative a constant. "
                + "If that constant is nonzero, the magnitude of the derivative tends to infinity at "
                + "the antipode. A one-sided comparison with a reciprocal power excludes every finite limit "
                + "of the original kernel there when D is at least four."),
            Entry("unscaled-derivative", "ds_unscaled_blowup", "Lower bound near the tip",
                "For κ > 1 and κu ≤ (κ − 1)T/2, the negative derivative of u raised to 1 − κ "
                + "and divided by T − u is at least (κ − 1)/(2T) times u raised to −κ."),
            Entry("unscaled-counterexample", "ds_unscaled_bound_counterexample",
                "Interior zero of the unscaled derivative",
                "In dimension five, the unscaled radial derivative vanishes at T/3. "
                + "Its magnitude therefore fails the proposed positive lower bound on the entire half interval."),
            Entry("modular-radius", "dsModularRadius", "Radius in modular coordinates",
                "Use the logistic map of slope 2π and range (0, L).", DescribeRole.Definition),
            Entry("unscaled-kernel", "dsUnscaledModularKernel", "Unscaled leading radial kernel",
                "Multiply the signed unscaled derivative by the modular Jacobian.",
                DescribeRole.Definition),
            Entry("unscaled-packet", "ds_unscaled_packet_diverges", "Translation toward the tip",
                "A nonnegative, nonzero smooth compactly supported packet has an unbounded pairing with "
                + "the signed leading radial term as it translates toward the tip. Its weighted Fourier "
                + "square integral is invariant under the same translations."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
