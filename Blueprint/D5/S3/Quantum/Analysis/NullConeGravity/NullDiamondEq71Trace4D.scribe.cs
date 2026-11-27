using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class NullDiamondEq71Trace4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform comparison and the finite relative covariance trace in four dimensions.",
        H("Symmetric forms and the massive reference norm"),
        Blocks(
            Entry("ambient-symmetric", "nullN", "Ambient symmetric covariance",
                "Add the massive correction to the identity.", DescribeRole.Definition),
            Entry("ambient-coercivity", "nullN_coercive", "Ambient coercivity",
                "The Hilbert–Schmidt correction, injective skew multiplier and two signed positive bounds supply a strictly positive lower bound for the symmetric covariance."),
            Entry("compressed-symmetric", "compressedN", "Compressed covariance",
                "Compress the ambient symmetric covariance by the inclusion of a complete complex subspace and its adjoint.", DescribeRole.Definition),
            Entry("massless-square", "mu0Sq", "Massless symmetric square",
                "Take the squared norm of a vector in the subspace.", DescribeRole.Definition),
            Entry("massive-square", "mumSq", "Massive symmetric square",
                "Take the real quadratic form of the compressed covariance.", DescribeRole.Definition),
            Entry("upper-comparison", "mumSq_le", "Upper comparison",
                "The operator norm of the ambient symmetric covariance bounds the massive square by the massless square, using the isometric inclusion and the inner product inequality."),
            Entry("inverse-root", "invRootN", "Inverse covariance root",
                "Take the ring inverse of the positive square root of the compressed covariance. Coercivity ensures that this square root is a unit.", DescribeRole.Definition),
            Entry("reference-map", "referenceMap", "Reference map",
                "Compose the subspace inclusion with the inverse covariance root.", DescribeRole.Definition),
            Entry("relative-symmetric", "relativeQ", "Relative symmetric covariance",
                "Transport the identity by congruence with the reference map.", DescribeRole.Definition),
            Entry("relative-skew", "relativeR", "Relative skew form",
                "Transport the skew multiplier by congruence with the reference map and multiply by the imaginary unit.", DescribeRole.Definition),
            Entry("root-difference", "eq71Delta", "Relative root difference",
                "Subtract the positive covariance square roots in the massive reference representation.", DescribeRole.Definition),
            Entry("uniform-relative-bound", "nullDiamond_eq71_4D", "Uniform finite-trace bound",
                "For positive mass and length, a single positive lower comparison constant applies to all complete complex subspaces. The inverse root normalizes the massive symmetric covariance to the identity. The transported relative symmetric covariance is invertible with trivial kernel, both covariance operators are positive, and the quarter-power congruence estimate bounds the squared Hilbert–Schmidt norm of their root difference by the inverse comparison constant times the squared weighted correction norm."),
            Entry("trace-identity", "eq71_trace_eq_hsSq", "Literal operator trace",
                "The difference of the two positive roots is self-adjoint and Hilbert–Schmidt. Its square is trace class. Evaluating the trace in a Hilbert basis gives the sum of squared image norms, equal to the squared Hilbert–Schmidt norm as a complex scalar."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
