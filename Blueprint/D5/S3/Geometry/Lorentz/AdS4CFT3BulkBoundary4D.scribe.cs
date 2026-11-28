using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class AdS4CFT3BulkBoundary4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Lorentz/AdS4CFT3BulkBoundary4D.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Observer/witten1998holography");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four-dimensional Anti-de Sitter geometry and scalar kernels.",
        H("Four-dimensional Anti-de Sitter geometry and scalar kernels"),
        Blocks(
            Paragraph(Text("The ambient signature has two negative directions. The Poincare chart takes positive height, and the conformal factor extends to height zero. The indicial inequality concerns real roots. The Euclidean kernel is evaluated away from its boundary insertion in the limit, and the Lorentzian kernel uses the region of positive quadratic denominator.")),
            Entry("so23-isometry-finrank-10", "so23_isometry_finrank_10", "Ten ambient orthogonal generators",
                "The signature-two-three infinitesimal stabilizer has dimension ten and its elementary generators satisfy the signed matrix commutator formula."),
            Entry("so23-preserves-ads4", "so23_preserves_ads4", "Ambient form preservation",
                "A matrix preserving the signed metric preserves the ambient quadratic form and each radius level."),
            Entry("poincareembed-on-ads4", "poincareEmbed_on_ads4", "Poincare patch on the hyperboloid",
                "For positive radius and height, the image is on the ambient level and its first plus last coordinate equals the positive radius squared divided by height."),
            Entry("poincareembed-metric-pullback", "poincareEmbed_metric_pullback", "Poincare metric on coordinate curves",
                "The derivative of a differentiable chart curve has the explicit ambient tangent. Its ambient square is the Minkowski coordinate speed square times the radius squared divided by the height squared."),
            Entry("ads4-timelike-conformal-boundary", "ads4_timelike_conformal_boundary", "Spacelike boundary normal",
                "The conformal factor vanishes at zero height, where its derivative is the nonzero reciprocal radius and the normal square is the positive reciprocal radius squared."),
            Entry("radial-light-travel", "radial_light_travel", "Finite coordinate travel time",
                "Starting at positive height, unit inward radial coordinate speed is null throughout the bulk segment and its first zero of height occurs at the initial height in coordinate time."),
            Entry("radial-proper-distance", "radial_proper_distance", "Proper radial distance",
                "Integrating the radius divided by height between positive heights gives the radius times the logarithm of the endpoint ratio."),
            Entry("radial-proper-distance-diverges", "radial_proper_distance_diverges", "Infinite spatial distance to the boundary",
                "For positive radius and fixed bulk height, the logarithmic distance tends to positive infinity as the lower endpoint tends to zero from above."),
            Entry("radial-affine-null-line", "radial_affine_null_line", "Affine null geodesic",
                "After replacing the radial height by the reciprocal of the affine parameter plus the reciprocal of the initial height, the ambient curve is a straight line with null direction."),
            Entry("bf-bound-real-dimension-iff", "bf_bound_real_dimension_iff", "Breitenlohner–Freedman indicial threshold",
                "A real conformal dimension exists exactly when mass squared times radius squared is at least minus nine quarters."),
            Entry("bf-indicial-roots", "bf_indicial_roots", "Both indicial roots",
                "At and above the threshold, the listed minus and plus dimensions exhaust the real roots. They sum to three and multiply to minus the scaled mass squared."),
            Entry("bf-root-separation", "bf_root_separation", "Coincidence at the threshold",
                "The minus root is strictly below the plus root exactly above the threshold. Both are three halves at the threshold."),
            Entry("bf-unitarity-dual-quantization-window", "bf_unitarity_dual_quantization_window", "Real roots satisfying scalar unitarity",
                "Real indicial roots both satisfy the scalar dimension inequality precisely when the scaled mass squared lies between minus nine quarters and minus five quarters, inclusively."),
            Entry("bf-strict-lower-dimension", "bf_strict_lower_dimension", "Strict scalar dimension inequality",
                "The lower dimension is above one half when the scaled mass squared is below minus five quarters. The real-root condition gives its physical domain."),
            Entry("bf-conformal-mass", "bf_conformal_mass", "Conformally coupled dimensions",
                "Scaled mass squared minus two gives dimensions one and two."),
            Entry("ads4-propagator-solves-klein-gordon", "ads4_propagator_solves_klein_gordon", "Klein–Gordon equation on both signatures",
                "On positive height and positive denominator, the four directional first and second derivatives have the stated slope and curvature expressions. With the time coefficient squared equal to one, the curved wave operator gives the kernel multiplied by the dimension times the dimension minus three, divided by the radius squared."),
            Entry("ads4-propagator-boundary-limit", "ads4_propagator_boundary_limit", "Boundary two-point power",
                "At nonzero Euclidean separation the kernel multiplied by the inverse height power converges from positive height to the separation norm raised to minus twice the dimension."),
            Entry("ads4-propagator-boundary-scaling-and-inversion", "ads4_propagator_boundary_scaling_and_inversion", "Kernel scaling and bulk inversion",
                "Positive simultaneous coordinate scaling gives weight minus the dimension. Inversion preserves positive height and denominator, is involutive, preserves the metric square on transformed tangent vectors, and expresses the kernel as the inverted height power."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}
