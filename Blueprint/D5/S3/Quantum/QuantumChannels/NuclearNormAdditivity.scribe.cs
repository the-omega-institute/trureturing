using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class NuclearNormAdditivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/NuclearNormAdditivity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For nonzero real vector families and positive weights, nuclear-norm additivity holds exactly when their normalized Gram matrices agree.",
        H("Real rectangular nuclear-norm additivity"),
        Blocks(
            Entry("polar", "exists_real_rectangular_polar", "A real rectangular polar contraction",
                "For any real rectangular matrix A, a contraction Z takes the positive square root of A transpose times A to A, and A and that square root have the same norm on every input vector. The construction descends the correspondence between their ranges to a linear isometry and composes it with orthogonal projection. Rectangular matrices, zero matrices and zero dimensional spaces are included.", DescribeRole.Theorem),
            Entry("dual-pairing", "dualPairing", "The trace pairing",
                "The pairing is the real linear trace of the composite of the adjoint of Z with the Euclidean linear map associated with A. The norm on Z is the operator norm induced by the Euclidean norms.", DescribeRole.Definition),
            Entry("nuclear-duality", "traceNorm_eq_max_dualPairing", "The trace norm is attained by a contraction",
                "The actual trace norm is the trace of the positive square root of A transpose times A, as defined by the frozen FiniteTraceDistance module. The theorem constructs a contraction attaining this trace pairing and proves that every contraction gives a pairing at most the trace norm. Its proof diagonalizes the positive square root, applies Cauchy-Schwarz to every eigenvector and uses the polar contraction for attainment. Duality is a conclusion of the proof, not a hypothesis.", DescribeRole.Theorem),
            Entry("weighted-outer", "weightedOuter", "Weighted rank-one expansions",
                "For a finite outcome type, weightedOuter is the sum of u times the real outer products x y transpose. The input and output index types are arbitrary finite types and may have different cardinalities.", DescribeRole.Definition),
            Entry("nuclear-bound", "traceNorm_weightedOuter_le", "The weighted rank-one nuclear bound",
                "With nonnegative weights, the trace norm of the weighted outer-product sum is bounded by the sum of u times the product of the vector lengths. No vector is required to be nonzero for this inequality. This follows from the proved duality theorem and the contraction estimate for each pairing.", DescribeRole.Theorem),
            Entry("additivity", "traceNorm_weightedOuter_eq_iff_normalized_gram", "Kopel's v2 Lemma 4",
                "For nonzero finite real vector families and strictly positive weights, the nuclear bound is an equality if and only if every pair of normalized x vectors has the same real inner product as the corresponding pair of normalized y vectors. This is Lemma 4 of Eran Kopel's supplied v2 additions. Necessity uses a maximizing contraction, and sufficiency uses the common-contraction criterion of WeightedGramContraction together with the proved upper and lower dual bounds. Repeated and dependent vectors and arbitrary positive weights are allowed. No basis, independence, or distinctness hypothesis is introduced. This establishes the additivity lemma; the channel equality characterization of Theorem 5 has additional dependencies.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string declaration, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumChannels/kopel2026sharpnorm")),
            Blocks(Paragraph(Text(text))), role);
}
