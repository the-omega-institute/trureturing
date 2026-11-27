using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class CCRGaussianExtensionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coercivity, common pure Gaussian extension, and square-summable squeezing.",
        H("A common pure extension for two Gaussian covariances"),
        Blocks(
            Paragraph(Text("On a complex Hilbert space with a real conjugation, the reference covariance is "
                + "the identity, the target covariance is Q, and R is their common real skew-adjoint operator. "
                + "The Hilbert–Schmidt difference of the signed covariance square roots is the condition in "
                + "Eq. (71) of Satishchandran and Sorce.")),
            Entry("coercivity", "covariance_coercive", "Coercivity from a covariance root difference",
                "For positive Q with trivial kernel, positive signed covariances, and a Hilbert–Schmidt "
                + "root difference, Q differs from the identity by a Hilbert–Schmidt operator. The difference "
                + "of squares factors through the root difference on both sides. The compact Fredholm "
                + "alternative gives invertibility and positivity gives a strictly positive scalar lower bound. "
                + "The positive square root is invertible, and both it and its inverse differ from the identity "
                + "by Hilbert–Schmidt operators."),
            Entry("normalized-skew", "normalizedSkew", "Normalized skew operator",
                "Multiply R on both sides by the inverse of the positive covariance square root.",
                DescribeRole.Definition),
            Entry("defect-root", "defectRoot", "Positive defect root",
                "Take the positive square root of one plus the square of the normalized skew operator.",
                DescribeRole.Definition),
            Entry("normalization", "normalized_properties", "Signed roots and the defect contraction",
                "For a real positive invertible covariance and real skew-adjoint R, positivity of the minus "
                + "signed covariance gives a normalized skew contraction. Conjugation gives positivity of the "
                + "plus signed operator. The two signed roots commute, their product is the defect root, "
                + "and the latter is real and lies between zero and the identity."),
            Entry("defect-comparison", "defectRoot_sub_hs", "Hilbert–Schmidt defect difference",
                "Right multiplication by the inverse covariance root gives two operators with Hilbert–Schmidt "
                + "difference. Their absolute values are the two normalized minus signed roots. "
                + "The absolute-value estimate compares these roots. Conjugation compares the plus roots, "
                + "and expansion of the difference of the two products gives the defect comparison."),
            Entry("doubling", "doubleCovariance", "Doubled covariance",
                "Conjugate one plus the defect root by the positive covariance root.", DescribeRole.Definition),
            Entry("reference-doubling", "doubleCovariance_one", "Reference doubled covariance",
                "At the identity covariance, the doubled covariance is one plus the positive square root "
                + "of one plus the square of the original skew operator."),
            Entry("doubling-properties", "doubleCovariance_properties", "Doubled covariance bounds and restriction",
                "The doubled covariance D is real and invertible and lies between Q and twice Q. "
                + "The normalized skew operator commutes with the defect root. The product of one plus "
                + "and one minus the defect is minus the square of the normalized skew operator. Consequently "
                + "half of D minus R D inverse R is exactly Q."),
            Entry("doubling-comparison", "doubleCovariance_sub_hs", "Hilbert–Schmidt doubling difference",
                "Hilbert–Schmidt comparison of the defect roots and of the positive covariance root with "
                + "the identity implies Hilbert–Schmidt comparison of the doubled covariances."),
            Entry("phase-embedding", "phaseEmbedding", "Common real phase-space map",
                "Send a fixed real vector f to the pair (f, Rf) divided by the square root of two.",
                DescribeRole.Definition),
            Entry("phase-embedding-injective", "phaseEmbedding_injective", "Injective real phase-space map",
                "Equality of the first coordinates forces equality of the original vectors. The argument "
                + "allows a kernel for the common skew operator."),
            Entry("pure-extension", "pureExtension", "Pure extension coordinates",
                "The real-linear equivalence sends (p, v) to the positive square root of D applied to p "
                + "minus the imaginary unit times the inverse root applied to v.", DescribeRole.Definition),
            Entry("restricted-inner-product", "pureExtension_inner", "Covariance of the embedded real data",
                "The inner product of the extended images of f and g is the original covariance pairing "
                + "minus the imaginary unit times the pairing with R. The two cross terms agree by "
                + "skew-adjointness. The diagonal terms combine using the doubled covariance identity."),
            Entry("squeeze-transition", "squeezeTransition", "Transition on the real coordinate",
                "Multiply the positive target doubled root by the inverse of the positive reference "
                + "doubled root.", DescribeRole.Definition),
            Entry("squeeze-metric", "squeezeTransition_properties", "Transition metric",
                "For real positive invertible doubled covariances with Hilbert–Schmidt difference, "
                + "the transition L is real and invertible. Its metric is bounded below by a positive "
                + "multiple of the identity and its difference from the identity is real, self-adjoint, "
                + "and Hilbert–Schmidt."),
            Entry("squeeze-eigenbasis", "exists_squeeze_eigenbasis", "Square-summable squeeze eigenbasis",
                "On a separable Hilbert space, restrict the metric perturbation to the fixed real subspace "
                + "and diagonalize it as a compact self-adjoint operator. The logarithms of its shifted "
                + "positive eigenvalues, divided by two, are square-summable. The squared norm of the "
                + "transition of any vector is the sum over the complexified basis of its squared real "
                + "coefficients weighted by exp(2r) and squared imaginary coefficients weighted by exp(-2r)."),
            Entry("common-extension", "commonPureExtension", "Common pure Gaussian extension",
                "For positive Q with trivial kernel, positive signed covariances with Hilbert–Schmidt root "
                + "difference determine two "
                + "real-linear pure coordinates on the same doubled phase space. Their restrictions along the "
                + "common embedding give the two original complex covariance pairings. The transition between "
                + "the pure coordinates admits the countable squeeze expansion with square-summable squeeze parameters."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
