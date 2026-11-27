using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Gauge;

internal sealed class YangMillsBPSSelfDual4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/LieTheory/belavinpolyakovschwartztyupkin1975pseudoparticles");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Euclidean Hodge duality, Yang-Mills action bounds, and exact BPST normalization.",
        H("Self-duality and the four-dimensional instanton"),
        Blocks(
            Paragraph(Text("Use three electric and three oriented magnetic coordinates for each color. "
                + "The oriented pairs are 01, 02, 03, 23, 31, 12. The Euclidean pairing uses "
                + "unit color weights. The BPST trace pairing multiplies this pairing by one half.")),
            Entry("hodge", "hodge4", "Hodge duality", "Exchange the electric and magnetic coordinates.", DescribeRole.Definition),
            Entry("pairing", "inner4", "Euclidean pairing", "Sum the products of matching electric and magnetic coordinates over all colors.", DescribeRole.Definition),
            Entry("norm", "normSq", "Squared length", "Pair a two-form with itself.", DescribeRole.Definition),
            Entry("top-density", "topDensity", "Topological density", "Pair the two-form with its Hodge dual.", DescribeRole.Definition),
            Entry("self-part", "selfDualPart", "Self-dual projection", "Take one half of the sum of the form and its dual.", DescribeRole.Definition),
            Entry("anti-part", "antiSelfDualPart", "Anti-self-dual projection", "Take one half of the difference of the form and its dual.", DescribeRole.Definition),
            Entry("coordinate-dimension", "hodge4_coordinate_iff", "Dimension selection", "The complementary degree of a two-form is two exactly when the coordinate index is equivalent to four coordinates."),
            Entry("involution", "hodge4_involutive", "Involution", "Applying the Hodge exchange twice gives the original form."),
            Entry("isometry", "hodge4_isometry", "Isometry", "Hodge exchange preserves the pairing of any two forms."),
            Entry("orthogonal", "sd_asd_orthogonal", "Orthogonality", "The inner product of the two projected parts is zero."),
            Entry("split", "sd_asd_orthogonal_split", "Orthogonal splitting", "The projected parts sum to the original form, have Hodge eigenvalues one and minus one respectively, and are orthogonal."),
            Entry("sum", "norm_sq_eq_sd_add_asd", "Action density decomposition", "Squared length is the sum of the squared lengths of the two projected parts."),
            Entry("difference", "topological_density_eq_sd_sub_asd", "Charge density decomposition", "Topological density is the squared length of the self-dual part minus that of the anti-self-dual part."),
            Entry("identity", "ym_bps_pointwise_identity", "Bogomolny identities", "Squared length equals half the squared length of the difference with the dual plus the topological density. It also equals half the squared length of the sum with the dual minus that density."),
            Entry("bound", "ym_bps_pointwise_bound", "Pointwise bound", "Absolute topological density is bounded by squared length."),
            Entry("equality", "ym_bps_equality_iff", "Pointwise equality", "Equality with positive signed density holds exactly for self-dual forms. Equality with negative signed density holds exactly for anti-self-dual forms."),
            Entry("action-bound", "ym_bps_action_bound", "Integrated bound", "For a measurable field of finite action on four-dimensional Euclidean space, absolute integrated charge density is bounded by the integrated squared length."),
            Entry("action-equality", "ym_bps_action_equality_iff", "Integrated equality", "For a continuous field of finite action, equality with the signed charge integral holds exactly when the field is self-dual everywhere. A nonnegative continuous difference with zero integral is identically zero."),
            Entry("matrix", "toTwoForm", "Antisymmetric tensor", "Place the electric and oriented magnetic entries into their indicated coordinate pairs and fill the reversed pairs with the negative entries.", DescribeRole.Definition),
            Entry("antisymmetric", "toTwoForm_antisymmetric", "Antisymmetry", "Swapping the two tensor indices negates each component."),
            Entry("tensor-norm", "normSq_tensor", "Tensor pairing normalization", "Squared length equals one half of the sum of squares over all colors and both tensor indices."),
            Entry("stress", "ymStress", "Stress tensor", "Contract the tensor over its second index and color, subtracting one quarter of the full norm sum times the Kronecker delta.", DescribeRole.Definition),
            Entry("trace", "ym_stress_trace_zero", "Trace cancellation", "The sum of the four diagonal stress entries is zero."),
            Entry("sd-stress", "selfDual_ym_stress_zero", "Self-dual stress cancellation", "Every stress entry vanishes for a self-dual form."),
            Entry("asd-stress", "antiSelfDual_ym_stress_zero", "Anti-self-dual stress cancellation", "Every stress entry vanishes for an anti-self-dual form."),
            Entry("eta", "thooftEta", "Self-dual eta symbols", "Both sets of three coordinates are the color Kronecker delta.", DescribeRole.Definition),
            Entry("eta-self-dual", "thooftEta_selfDual", "Eta self-duality", "Hodge exchange fixes the eta symbols."),
            Entry("profile", "bpstField", "BPST profile", "Multiply eta by four times the squared scale divided by the square of the sum of squared radius and squared scale.", DescribeRole.Definition),
            Entry("profile-duality", "bpst_instanton_selfDual", "BPST self-duality", "The profile is self-dual at every point and scale."),
            Entry("profile-stress", "bpst_instanton_stress_zero", "BPST stress", "All stress entries of the profile vanish."),
            Entry("trace-action", "traceActionDensity", "Trace action density", "Use half the unit-pairing squared length.", DescribeRole.Definition),
            Entry("trace-charge", "traceTopDensity", "Trace charge density", "Use half the unit-pairing topological density.", DescribeRole.Definition),
            Entry("density", "bpst_density", "Exact radial density", "The trace action density is 48 times the fourth power of the scale divided by the fourth power of the sum of squared radius and squared scale."),
            Entry("action", "bpstAction", "Action", "Integrate trace action density over all four Euclidean coordinates.", DescribeRole.Definition),
            Entry("charge", "bpstCharge", "Normalized charge", "Divide integrated trace charge density by eight pi squared.", DescribeRole.Definition),
            Entry("finite-action", "bpst_instanton_finite_action", "Finite action", "The trace action density is integrable for every strictly positive scale."),
            Entry("exact-action", "bpst_instanton_exact_action", "Exact action", "For every strictly positive scale the action equals eight pi squared. The radial integral equals one twelfth and the round three-sphere contributes two pi squared."),
            Entry("exact-charge", "bpst_instanton_exact_charge_one", "Unit charge", "For every strictly positive scale the normalized charge equals one by self-duality and the exact action integral."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
