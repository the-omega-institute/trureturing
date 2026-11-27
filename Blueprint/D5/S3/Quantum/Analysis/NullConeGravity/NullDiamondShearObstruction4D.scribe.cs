using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class NullDiamondShearObstruction4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    private static readonly LibraryNoteRef Penrose =
        LibraryNoteRef.Create("D5/L/HilbertOperators/penrose1965planewaves");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact pre-caustic screen forms give a nonzero angular mismatch with inverse-square growth.",
        H("Ricci-flat plane-wave point-cone shear"),
        Blocks(
            Paragraph(Text("For positive tidal amplitude α, work with affine pairs 0 < u < v < π/α "
                + "on the point cone. The oscillatory and hyperbolic Jacobi factors yield two distinct "
                + "positive screen coefficients. This distinction gives a strictly positive axial "
                + "mismatch on every separated pre-caustic radial rectangle.")),
            Entry("rosen-oscillatory", "rosenP", "Oscillatory Rosen factor",
                "The factor at u is sin(αu) divided by α.", DescribeRole.Definition, focusing: true),
            Entry("rosen-hyperbolic", "rosenQ", "Hyperbolic Rosen factor",
                "The factor at u is sinh(αu) divided by α.", DescribeRole.Definition, focusing: true),
            Entry("vertex-jacobian", "rosen_vertex_jacobian", "Vertex Jacobi propagator",
                "The vertex Jacobian has the hyperbolic and oscillatory factors on its diagonal, "
                + "in that order.", focusing: true),
            Entry("oscillatory-jacobi", "rosenP_jacobi", "Oscillatory Jacobi equation",
                "For α > 0, the first derivative at u is cos(αu) and its derivative is −α² times "
                + "the oscillatory factor."),
            Entry("hyperbolic-jacobi", "rosenQ_jacobi", "Hyperbolic Jacobi equation",
                "For α > 0, the first derivative at u is cosh(αu) and its derivative is α² times "
                + "the hyperbolic factor."),
            Entry("tip-initial-conditions", "rosen_tip_initial_conditions", "Jacobi data at the tip",
                "For α > 0 both factors start at zero with unit affine derivative."),
            Entry("ricci-trace", "rosen_ricci_flat", "Cancellation of the Ricci trace",
                "At every positive affine parameter before the first caustic, the ratios of the "
                + "second derivatives to their factors are −α² and α². Their sum is zero."),
            Entry("synge-oscillatory", "syngeQx", "Oscillatory Synge coefficient",
                "Multiply the endpoint oscillatory factors by α(v−u) divided by sin(α(v−u)).",
                DescribeRole.Definition),
            Entry("synge-hyperbolic", "syngeQy", "Hyperbolic Synge coefficient",
                "Multiply the endpoint hyperbolic factors by α(v−u) divided by sinh(α(v−u)).",
                DescribeRole.Definition),
            Entry("oscillatory-screen-integral", "syngeQx_eq_integral", "Inverse oscillatory screen integral",
                "For 0 < u < v < π/α and α > 0, divide v−u by the integral of the inverse square "
                + "of the oscillatory factor. The antiderivative is −α cot(αu) at an affine argument u."),
            Entry("hyperbolic-screen-integral", "syngeQy_eq_integral", "Inverse hyperbolic screen integral",
                "For 0 < u < v and α > 0, divide v−u by the integral of the inverse square of the "
                + "hyperbolic factor. The antiderivative is −α coth(αu) at an affine argument u."),
            Entry("strict-screen-anisotropy", "syngeQx_lt_syngeQy", "Strict ordering of the screen coefficients",
                "The oscillatory coefficient is strictly positive and strictly below the hyperbolic "
                + "coefficient on every positive pre-caustic pair. The inverse-square oscillatory "
                + "integrand strictly exceeds its hyperbolic counterpart on the affine segment."),
            Entry("angular-factor", "hadamardAnisotropy", "Area-normalized angular factor",
                "Divide the square root of the product of the two screen coefficients by the "
                + "directional screen form with angular components cos θ and sin θ.",
                DescribeRole.Definition),
            Entry("rectangle-mismatch", "rectMismatch", "Radial rectangle mismatch",
                "The four-corner difference adds the upper-upper and lower-lower values and "
                + "subtracts the other two values of the angular factor.", DescribeRole.Definition),
            Entry("axis-factor", "hadamardAnisotropy_axis", "Angular factor on the oscillatory axis",
                "For a positive pre-caustic pair the value at θ = 0 equals the square root of "
                + "the hyperbolic coefficient divided by the oscillatory one."),
            Entry("axis-mismatch-positive", "rectMismatch_axis_pos", "Strictly positive axial mismatch",
                "Write the axial factor as the exponential of half the sum of log(sinh t / sin t) "
                + "at αu and αv minus the same function at α(v−u). The slope of this logarithmic "
                + "ratio is positive and strictly increasing on (0, π). Differentiation in u "
                + "shows that the axial difference between the two fixed v values strictly "
                + "increases from u₁ to u₂."),
            Entry("tip-rectangle", "exists_rectMismatch_ne_zero", "Nonzero rectangles arbitrarily near the tip",
                "For every positive cutoff δ at or below the first caustic, the four affine "
                + "parameters δ/5, 2δ/5, 3δ/5 and 4δ/5 give a nonzero axial mismatch."),
            Entry("poisson-parameter", "hadamardPoissonParameter", "Poisson parameter",
                "Divide the difference of the hyperbolic and oscillatory square roots by their sum.",
                DescribeRole.Definition),
            Entry("poisson-parameter-range", "hadamardPoissonParameter_mem_Ioo", "Strict Poisson parameter bounds",
                "Strict ordering of the positive screen coefficients places the parameter strictly "
                + "between zero and one."),
            Entry("poisson-representation", "hadamardAnisotropy_eq_poisson", "Poisson representation",
                "The angular factor equals the disk Poisson kernel with the stated parameter at "
                + "twice the screen angle."),
            Entry("angular-average", "hadamardAnisotropy_average", "Unit angular average",
                "The integral of the angular factor over a full turn, divided by 2π, is one for "
                + "each positive pre-caustic pair."),
            Entry("angular-inner-product", "hadamardAnisotropy_inner", "Exact angular inner product",
                "For two positive pre-caustic pairs with Poisson parameters s and t, the integral "
                + "of the product of their angular factors over a full turn is 2π(1+st)/(1−st)."),
            Entry("angular-mismatch-positive", "rectMismatch_integral_sq_pos", "Positive squared angular mismatch",
                "Continuity and the positive axial value give a strictly positive integral of "
                + "the squared mismatch over a full turn."),
            Entry("scalar-screen", "screen_zero_shear", "Zero shear for a scalar screen",
                "When two positive screen coefficients agree at all radial pairs, the normalized "
                + "angular factor is one at every angle and its four-corner difference is zero."),
            Entry("annulus-integral", "rectMismatch_annulus_squared", "Exact polar annulus integral",
                "For 0 < ε < ρ, the integral of the squared mismatch kernel with polar measure "
                + "equals half the squared angular integral times the difference of the "
                + "inverse squared radii, ε⁻²−ρ⁻²."),
            Entry("annulus-divergence", "rectMismatch_annulus_diverges", "Divergence at angular coincidence",
                "With a fixed positive outer radius, the annular square integral for every "
                + "separated pre-caustic radial rectangle tends to positive infinity as the "
                + "inner radius decreases to zero."),
            Entry("wedge-obstruction", "shear_kernel_not_L2_on_ball", "Inverse-square growth on a sector",
                "On two copies of a positive-radius screen ball, an almost-everywhere positive "
                + "inverse-square lower bound for the modulus at small nonzero separations "
                + "in a nonempty angular sector excludes square integrability for the product "
                + "of the restricted volume measures."),
            Entry("plane-wave-kernel", "planeWavePointConeShearKernel", "Plane-wave shear kernel",
                "For distinct screen endpoints, divide the angular mismatch at the displacement "
                + "angle by π² times the squared displacement norm.", DescribeRole.Definition),
            Entry("plane-wave-obstruction", "planeWave_pointCone_shear_not_L2", "Plane-wave obstruction on every screen ball",
                "A continuous angular mismatch with positive axial value gives a sector of "
                + "inverse-square growth. Every separated pre-caustic rectangle therefore "
                + "gives a shear kernel outside L² on every positive-radius screen ball."),
            Entry("hilbert-schmidt-kernel", "hilbertSchmidt_has_integral_kernel", "Kernel of a Hilbert–Schmidt operator",
                "On complex L² of an s-finite measure, a Hilbert–Schmidt operator is induced by "
                + "a square-integrable product kernel. The square-summable images of an orthonormal "
                + "basis give the kernel through an orthogonal series of separated factors."),
            Entry("off-diagonal-representation", "RepresentsKernelOffDiagonal", "Off-diagonal representation",
                "On positively separated measurable rectangles, the kernel is integrable and "
                + "its integral agrees with the operator pairing of the corresponding indicator "
                + "functions.", DescribeRole.Definition),
            Entry("operator-obstruction", "shear_obstruction_no_hilbertSchmidt_kernel", "Hilbert–Schmidt obstruction",
                "A Hilbert–Schmidt operator representing the wedge-singular kernel off the "
                + "diagonal would supply a square-integrable representative with the same "
                + "indicator pairings. These pairings determine the kernel almost everywhere "
                + "off the diagonal, where the inverse-square lower bound forces divergence."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem, bool focusing = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(),
            focusing ? AssessedProvenance.FromRepo(Source, Penrose) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
