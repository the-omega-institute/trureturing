using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class NullDiamondBesselStrip4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A separately holomorphic null-diamond correction with uniform exponential strip decay.",
        H("Complex modular strip and logarithmic correction"),
        Blocks(
            Paragraph(Text("The modular coordinate in the four-dimensional scalar covariance problem of "
                + "Satishchandran and Sorce allows the radial logarithmic correction to extend to a complex strip. "
                + "The lifted logarithm of each modular radius yields a holomorphic expression even when their "
                + "product crosses the cut of the principal logarithm.")),
            Entry("strip-width", "stripB", "Closed strip half-width",
                "The real constant b equals 3/8.", DescribeRole.Definition),
            Entry("modular-radius", "modularU", "Complex modular radius",
                "For complex z, U(z) = exp(2πz)/(1 + exp(2πz)).", DescribeRole.Definition),
            Entry("modular-jacobian", "modularUprime", "Modular Jacobian",
                "For complex z, U′(z) = 2π exp(2πz)/(1 + exp(2πz))².", DescribeRole.Definition),
            Entry("lifted-logarithm", "liftedLog", "Lifted logarithm of the modular radius",
                "For complex z, L(z) = 2πz − log(1 + exp(2πz)), where log is the principal complex logarithm.",
                DescribeRole.Definition),
            Entry("open-strip", "openStrip", "Open strip",
                "The open strip is the set of complex points z with |Im z| < 1/2.", DescribeRole.Definition),
            Entry("closed-strip", "closedStrip", "Closed strip",
                "The closed strip is the set of complex points z with |Im z| ≤ b.", DescribeRole.Definition),
            Entry("strip-correction", "stripG", "Complex modular correction",
                "For real M and x and complex z and w with x < 1, put t = M² U(z) U(w)(1−x)/2 "
                + "and ℓ = log(M²(1−x)/2) + L(z) + L(w), using the real logarithm in the first term. "
                + "The kernel G_M(z,w,x) equals 4 U′(z) U′(w) times the correction with supplied logarithm ℓ "
                + "at argument t. Its value for x ≥ 1 is zero.", DescribeRole.Definition),
            Entry("denominator-bound", "strip_denom_lower", "Uniform lower bound for the modular denominator",
                "For every z in the closed strip, the norm of 1 + exp(2πz) is at least "
                + "cos(πb)(1 + exp(2π Re z)). Rotating the denominator by exp(−iπ Im z) exhibits "
                + "the real part (1 + exp(2π Re z)) cos(π Im z), and cosine is bounded below by cos(πb)."),
            Entry("exponentiate-lift", "exp_liftedLog", "The lifted logarithm exponentiates to the modular radius",
                "For every z in the open strip, exp(L(z)) = U(z). The modular denominator belongs to the "
                + "slit domain of the complex logarithm there."),
            Entry("real-axis-correction", "stripG_real", "Agreement with the real radial correction",
                "For real M, r, s and x with M > 0 and x < 1, G_M(r,s,x) equals 4 U′(r) U′(s) "
                + "times the real radial correction at M, Re U(r), Re U(s) and x. On the real axis each "
                + "modular radius is positive and its lifted logarithm agrees with the ordinary real logarithm."),
            Entry("left-holomorphy", "stripG_diff_left", "Holomorphy in the first modular coordinate",
                "For every real M and x and complex w, the function z ↦ G_M(z,w,x) is complex differentiable "
                + "on the open strip. The modular radius, Jacobian and lifted logarithm are holomorphic there, "
                + "and the two weighted power-series coefficients are entire."),
            Entry("right-holomorphy", "stripG_diff_right", "Holomorphy in the second modular coordinate",
                "For every real M and x and complex z, the function w ↦ G_M(z,w,x) is complex differentiable "
                + "on the open strip."),
            Entry("strip-decay", "stripG_bound", "Uniform exponential decay on the closed strip",
                "For every real M > 0 there exists a real C > 0 such that for all complex z and w in the "
                + "closed strip and every real x with −1 ≤ x < 1, the norm of G_M(z,w,x) is at most "
                + "C exp(−2π(|Re z| + |Re w|)) (1 + |Re z| + |Re w| + |log(1−x)|). "
                + "The denominator bound controls the radii uniformly and supplies an exponential bound for "
                + "each Jacobian. The real and imaginary parts of the principal logarithm bound each lifted "
                + "logarithm by a constant times 1 + |Re z|. The series argument stays in a fixed bounded disk "
                + "and the entire coefficient functions are bounded on its closure. The two Jacobian factors "
                + "therefore give the required exponential decay while the angular logarithm remains explicit."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
