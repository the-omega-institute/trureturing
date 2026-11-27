using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class CCRConjugationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fixed real Hilbert space of a conjugation and the transport of bounded operators and Hilbert–Schmidt sums.",
        H("Real conjugation and operator restriction"),
        Blocks(
            Paragraph(Text("An antiunitary involution gives a real form of a complex Hilbert space. Its fixed vectors carry the real Hilbert norm, and each complex vector decomposes uniquely into a fixed real part plus the imaginary unit times a fixed real part.")),
            Entry("real-conjugation", "RealConjugation", "Real conjugation",
                "A real linear isometric equivalence is involutive and sends a complex scalar multiple to the conjugate scalar times the image vector.", DescribeRole.Definition),
            Entry("fixed-real-space", "realSubspace", "Fixed real subspace",
                "The real submodule is the set of vectors fixed by the conjugation.", DescribeRole.Definition),
            Entry("fixed-space-closed", "realSubspace_isClosed", "Closed real form",
                "The fixed real subspace is closed, since it is the equality set of two continuous maps."),
            Entry("fixed-space-inner-product", "realSubspaceInnerProductSpace", "Real inner product space",
                "The fixed real subspace inherits the real part of the ambient complex inner product.", DescribeRole.Definition),
            Entry("fixed-space-completeness", "realSubspaceComplete", "Completeness of the real form",
                "When the ambient space is complete, the fixed real subspace is complete because it is closed.", DescribeRole.Definition),
            Entry("real-part", "realPart", "Real part",
                "The real part is one half of the vector plus its conjugate.", DescribeRole.Definition),
            Entry("imaginary-part", "imagPart", "Imaginary part",
                "The imaginary part is the vector minus its conjugate divided by twice the imaginary unit.", DescribeRole.Definition),
            Entry("real-part-fixed", "realPart_mem", "Fixed real part",
                "The real part lies in the fixed real subspace."),
            Entry("imaginary-part-fixed", "imagPart_mem", "Fixed imaginary part",
                "The imaginary part lies in the fixed real subspace."),
            Entry("real-imaginary-decomposition", "real_imag_decomposition", "Real and imaginary decomposition",
                "Every vector is the sum of its real part and the imaginary unit times its imaginary part."),
            Entry("unique-decomposition", "real_imag_unique", "Uniqueness of the decomposition",
                "Any decomposition into a fixed real vector plus the imaginary unit times another fixed real vector yields exactly the real and imaginary parts."),
            Entry("conjugated-inner-product", "conj_inner", "Antiunitary inner product",
                "The complex inner product of two conjugated vectors equals the conjugate of their complex inner product."),
            Entry("real-inner-product", "real_inner", "Inner product of fixed vectors",
                "The complex inner product of fixed vectors is the real inner product embedded into the complex numbers."),
            Entry("norm-decomposition", "norm_sq_decomposition", "Squared norm decomposition",
                "The squared norm of every vector equals the sum of the squared norms of its real and imaginary parts."),
            Entry("conjugate-operator", "conjOp", "Conjugate bounded operator",
                "Applying the conjugation before and after a bounded complex linear operator defines another bounded complex linear operator.", DescribeRole.Definition),
            Entry("operator-action", "conjOp_apply", "Conjugate operator action",
                "At each vector the conjugate operator applies the conjugation, the original operator, and the conjugation in order."),
            Entry("conjugate-adjoint", "conjOp_adjoint", "Conjugation and adjoints",
                "The adjoint of the conjugate operator equals the conjugate of the adjoint."),
            Entry("conjugate-composition", "conjOp_comp", "Conjugation and composition",
                "Conjugation preserves operator composition, because the two consecutive involutions cancel."),
            Entry("conjugate-positivity", "conjOp_nonneg", "Positivity under conjugation",
                "The conjugate of a nonnegative bounded operator is nonnegative."),
            Entry("real-restriction", "restrictReal", "Real operator restriction",
                "A complex linear bounded operator commuting with the conjugation restricts to a real linear bounded map of the fixed real Hilbert space into itself.", DescribeRole.Definition),
            Entry("restriction-action", "restrictReal_apply", "Action of the real restriction",
                "The underlying complex vector of the restriction applied to a fixed vector is its image under the original operator."),
            Entry("restriction-norm", "restrictReal_norm", "Equal real and complex norms",
                "For an operator commuting with the conjugation, the operator norm on the fixed real Hilbert space equals its complex operator norm. The squared norm decomposition transfers the bound from fixed vectors to arbitrary vectors."),
            Entry("adjoint-reality", "adjoint_commutes", "Reality of the adjoint",
                "If an operator commutes with the conjugation then its adjoint also commutes with it."),
            Entry("restriction-adjoint", "restrictReal_adjoint", "Adjoint of the real restriction",
                "Restricting the adjoint to the fixed real Hilbert space gives the adjoint of the real restriction."),
            Entry("restriction-self-adjoint", "restrictReal_selfAdjoint", "Self-adjointness of the real restriction",
                "The restriction of a self-adjoint operator commuting with conjugation is self-adjoint."),
            Entry("restriction-positivity", "restrictReal_nonneg", "Positivity of the real restriction",
                "The restriction of a nonnegative operator commuting with conjugation is nonnegative."),
            Entry("restriction-skew-adjoint", "restrictReal_skewAdjoint", "Skew-adjointness of the real restriction",
                "The restriction of a skew-adjoint operator commuting with conjugation is skew-adjoint."),
            Entry("complex-basis", "complexHilbertBasis", "Complex Hilbert basis from a real Hilbert basis",
                "The same vectors of any real Hilbert basis of the fixed subspace define a complex Hilbert basis of the ambient space.", DescribeRole.Definition),
            Entry("complex-basis-vectors", "complexHilbertBasis_apply", "Identical basis vectors",
                "Each vector of the complex Hilbert basis is exactly the underlying ambient vector of the corresponding real Hilbert basis."),
            Entry("countable-real-basis", "exists_countable_realHilbertBasis", "Countable real Hilbert basis",
                "For a separable ambient complex Hilbert space, the fixed real Hilbert space admits a Hilbert basis on a countable index set."),
            Entry("restriction-hilbert-schmidt-sum", "restrictReal_hasSum_hsSq", "Convergent Hilbert–Schmidt sum",
                "For a Hilbert–Schmidt complex operator commuting with conjugation, the sum of the squared norms of its real restriction along any real Hilbert basis converges to the complex Hilbert–Schmidt squared norm."),
            Entry("restriction-hilbert-schmidt", "restrictReal_hsSq", "Preservation of the Hilbert–Schmidt square sum",
                "For a Hilbert–Schmidt complex operator commuting with the conjugation, the squared norm sum of its real restriction along any real Hilbert basis equals the complex Hilbert–Schmidt squared norm."),
            Entry("restriction-compact", "restrictReal_isCompact", "Compactness of the real restriction",
                "For a Hilbert–Schmidt complex operator commuting with the conjugation, its real restriction is compact."),
            Entry("null-conjugation", "nullDiamondRealConjugation", "Null-diamond real conjugation",
                "The isometric frequency-reflection conjugation on the four-dimensional phase Hilbert space supplies a real conjugation, with involution and conjugate scalar law inherited from the frequency action.", DescribeRole.Definition))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
