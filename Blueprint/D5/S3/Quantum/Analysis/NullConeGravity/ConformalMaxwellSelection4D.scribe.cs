using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class ConformalMaxwellSelection4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four-dimensional Maxwell transport and the exact transverse and longitudinal Proca weights.",
        H("Conformal Maxwell selection and de Sitter Proca modes"),
        Blocks(
            Paragraph(Text("Appendix B.1 of Satishchandran and Sorce gives the Minkowski characteristic "
                + "Maxwell flux and its radiative reference on the constrained space. The four-dimensional "
                + "comparison uses fixed characteristic coordinates and the transported Gaussian data.")),
            Entry("weight", "maxwellConformalWeight", "Maxwell conformal weight",
                "Raise the conformal scale to the integer exponent D − 4.", DescribeRole.Definition),
            Entry("density", "maxwell_density_scaling", "Volume and inverse metric factors",
                "For a positive scale the volume factor is Ωᴰ and each inverse metric factor is Ω⁻². "
                + "Their product is the Maxwell conformal weight."),
            Entry("single-scale", "maxwellConformalWeight_eq_one_at_iff", "Selection by a single scale",
                "At any positive Ω different from one the weight equals one exactly when D = 4."),
            Entry("all-scales", "maxwellConformalWeight_eq_one_iff", "Selection by all positive scales",
                "The weight equals one at every positive scale exactly when D = 4. "
                + "The forward implication can use Ω = 2."),
            Entry("field-contraction", "maxwellFieldContraction", "Raised field contraction",
                "Sum qᵢqⱼFᵢⱼ² over both indices, where q contains the inverse diagonal metric entries.",
                DescribeRole.Definition),
            Entry("stress", "maxwellStress", "Diagonal-chart Maxwell stress tensor",
                "Contract one field index using q. Subtract the covariant metric component times "
                + "one quarter of the full field contraction.", DescribeRole.Definition),
            Entry("stress-trace", "maxwell_stress_trace", "Stress trace identity",
                "For nonzero inverse metric entries the trace is (4 − D)/4 times the field contraction."),
            Entry("stress-selection", "maxwell_stress_trace_eq_zero_iff", "Stress trace selection",
                "For nonzero inverse metric entries and nonzero field contraction the trace vanishes "
                + "exactly in dimension four."),
            Entry("chart-divergence", "maxwellChartDivergence", "Density-coordinate divergence",
                "Differentiate the weighted reference-raised field in each chart coordinate, "
                + "sum over the first index, and divide by the volume scale Ωᴰ.", DescribeRole.Definition),
            Entry("four-divergence", "maxwell4D_divergence", "Four-dimensional divergence identity",
                "In dimension four the derivative acts on the reference-raised field alone, with "
                + "the factor Ω⁻⁴ outside the sum."),
            Entry("vacuum-equation", "maxwell4D_vacuum_equals_reference", "Source-free field equation",
                "At a point of positive conformal scale, the vanishing of every divergence component "
                + "is equivalent to the reference source-free equation."),
            Entry("screen-density", "maxwell_screen_density_scaling", "Conformal scaling of the screen density",
                "For a positive scale, multiply the cross-section volume weight Ω^(D − 2) by the "
                + "inverse screen metric weight Ω⁻² to obtain the Maxwell conformal weight."),
            Entry("flux", "maxwellCharacteristicFlux", "Characteristic Maxwell flux",
                "Integrate the antisymmetrized generator derivative paired by the reference "
                + "densitized inverse screen metric. Scale the cross-section volume by Ω^(D − 2) and "
                + "the inverse screen metric by Ω⁻². Use a plus sign in front of the oriented integral.", DescribeRole.Definition),
            Entry("symplectic", "maxwell4D_conformal_symplectic_invariant", "Characteristic symplectic invariance",
                "For a positive conformal scale in dimension four, the flux agrees with the flux at unit scale."),
            Entry("radiative-kernel", "maxwellRadiativeKernel", "Regulated radiative pairing",
                "Use Eq. (125) with the common constrained profiles and angular screen. Pair the "
                + "profiles at two generator times and the same angle, use the inverse-square "
                + "kernel (u₁ − u₂ − iε)⁻², and multiply the integral by −1/π. Include one "
                + "four-dimensional weight at each generator time.", DescribeRole.Definition),
            Entry("kernel-invariance", "maxwell4D_radiative_kernel_invariant", "Pointwise regulator invariance",
                "At every regulator the transported and reference radiative pairings agree."),
            Entry("states", "maxwell4D_conformal_states_equal", "Equality of the transported Gaussian states",
                "On a common Weyl system, normalized states whose Gaussian coefficients use the two "
                + "respective right limits of the regulated pairing agree. Uniqueness of the boundary "
                + "limit identifies the covariances on every Weyl generator."),
            Entry("defect", "maxwell4D_covariance_defect_zero", "Zero Hilbert–Schmidt defect",
                "If the matrix elements of two bounded operators realize the respective right limits "
                + "of the transported and reference kernels, uniqueness of the limit identifies "
                + "the operators. Their square-root difference is Hilbert–Schmidt with squared norm zero."),
            Entry("proca-exponent", "procaBeta", "Proca rescaling exponent",
                "Half the kinetic exponent, β = (D − 4)/2.", DescribeRole.Definition),
            Entry("proca-potential", "procaCurvaturePotential", "Transverse curvature coefficient",
                "The coefficient is β(β + 1).", DescribeRole.Definition),
            Entry("proca-factorization", "proca_curvature_potential_eq", "Factorization of the curvature coefficient",
                "Multiplying out gives (D − 4)(D − 2)/4."),
            Entry("proca-selection", "proca_curvature_potential_zero_iff", "Curvature cancellation",
                "For D ≥ 3 the curvature coefficient vanishes exactly in dimension four."),
            Entry("proca-transverse", "proca_transverse_rescaled_ode", "Transverse Proca equation",
                "For H > 0 and t < 0, use Ω = −1/(Ht) and v = ΩᵝA. The operator "
                + "(Ω^(D − 4)A′)′ + Ω^(D − 4)(k² + Ω²m²)A equals Ωᵝ[v″ + (k² + "
                + "Ω²m² − β(β + 1)/t²)v]. "
                + "The identity uses differentiability of A at negative times and of its derivative at t."),
            Entry("proca-long-density", "procaLongitudinalDensity", "Longitudinal quadratic density",
                "For temporal component a and longitudinal derivative u, add Ω^(D − 4)(u − ka)²/2 "
                + "and Ω^(D − 2)m²a²/2.", DescribeRole.Definition),
            Entry("proca-long-elimination", "proca_longitudinal_kinetic_weight", "Exact temporal-component elimination",
                "For positive Ω, k and m, put c = k² + Ω²m². The unique minimizer is a₀ = ku/c. "
                + "The minimum is Ω^(D − 4)Ω²m²u²/(2c), and the excess at any a is "
                + "Ω^(D − 4)c(a − a₀)²/2."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
