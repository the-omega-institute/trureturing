using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class NullDiamondExcitability5DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondExcitability5D.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sharp finite trace and mutual Gaussian excitability in five dimensions.",
        H("The sharp finite trace and mutual Gaussian excitability in five dimensions"),
        Blocks(
            Entry("null-n5d", "nullN5D", "Massive symmetric covariance",
                "The identity plus the five-dimensional correction represents the massive symmetric covariance.", DescribeRole.Definition),
            Entry("null-n5d-coercive", "nullN5D_coercive", "Uniform lower bound",
                "Both signed covariances are positive. The centered multiplier has trivial kernel and the massive correction is compact, so the massive symmetric covariance has a strictly positive scalar lower bound."),
            Entry("compressed-n5d", "compressedN5D", "Compressed covariance",
                "Compress the massive symmetric covariance by the inclusion of a complete complex subspace.", DescribeRole.Definition),
            Entry("mu0sq5d", "mu0Sq5D", "Squared reference norm",
                "The massless squared norm is the squared Hilbert space norm of the profile.", DescribeRole.Definition),
            Entry("mum-sq5d", "mumSq5D", "Squared massive norm",
                "The massive squared norm is the real part of the quadratic form of the compressed covariance.", DescribeRole.Definition),
            Entry("mum-sq5d-le", "mumSq5D_le", "Upper covariance comparison",
                "The massive squared norm is bounded by the massless squared norm times the norm of the ambient massive symmetric covariance."),
            Entry("inv-root-n5d", "invRootN5D", "Inverse covariance root",
                "Take the inverse of the positive square root of the compressed massive symmetric covariance.", DescribeRole.Definition),
            Entry("reference-map5d", "referenceMap5D", "Massive normalization map",
                "Compose the inverse square root with the complex subspace inclusion.", DescribeRole.Definition),
            Entry("relative-q5d", "relativeQ5D", "Relative massless covariance",
                "Congruence of the identity by the massive normalization map gives the massless symmetric form in the massive norm.", DescribeRole.Definition),
            Entry("relative-r5d", "relativeR5D", "Relative commutator",
                "Apply the same congruence to the centered multiplier and multiply by the imaginary unit.", DescribeRole.Definition),
            Entry("eq71delta5d", "eq71Delta5D", "Difference of covariance roots",
                "Subtract the positive massive Wightman square root from the positive massless Wightman square root in the massive norm.", DescribeRole.Definition),
            Entry("null-diamond-eq71-5d", "nullDiamond_eq71_5D", "Sharp trace estimate",
                "For every positive mass and radius, a single positive coercivity constant works for all complete complex subspaces. The relative covariance is a unit with trivial kernel and both Wightman operators are positive. The squared Hilbert–Schmidt norm of the root difference is at most the weighted correction square divided by the coercivity constant."),
            Entry("eq71-trace-eq-hs-sq-5d", "eq71_trace_eq_hsSq_5D", "Literal trace equality",
                "The square of the self-adjoint root difference is trace class. Its operator trace equals the squared Hilbert–Schmidt norm of the root difference."),
            Entry("subspace-conjugation5d", "subspaceConjugation5D", "Restricted real conjugation",
                "Restrict frequency reflection and complex conjugation to an invariant complex subspace.", DescribeRole.Definition),
            Entry("null-diamond-relative-properties5d", "nullDiamondRelativeProperties5D", "Relative Gaussian data",
                "On an invariant complete subspace, the relative symmetric covariance is real, positive and injective. The relative commutator is real and skew-adjoint. Both Wightman operators are positive and their root difference is Hilbert–Schmidt."),
            Entry("null-diamond-excitable-5d", "nullDiamond_excitable_5D", "Mutual Gaussian excitability",
                "Any Weyl system realizing the two relative Gaussian covariances with the common symplectic form and dense real data has both states in each other’s countable GNS folia."),
            Entry("null-diamond-concrete-realization5d", "NullDiamondConcreteRealization5D", "Concrete Gaussian pair",
                "Use the paired Fock Weyl realization with the relative covariances on the fixed real form of the subspace.", DescribeRole.Definition),
            Entry("null-diamond-concrete-gaussian-excitable-5d", "nullDiamond_concrete_gaussian_excitable_5D", "Concrete realization on invariant subspaces",
                "For positive mass and radius, every invariant complete complex subspace admits a concrete paired Weyl algebra with the two prescribed Gaussian states and mutual excitability."),
            Entry("null-diamond-full-space-excitable-5d", "nullDiamond_full_space_excitable_5D", "Concrete realization on the full space",
                "The full five-dimensional phase Hilbert space admits the paired Weyl realization of the two Gaussian states with mutual excitability."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
