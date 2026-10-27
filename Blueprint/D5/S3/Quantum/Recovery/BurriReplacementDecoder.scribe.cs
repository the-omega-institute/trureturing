using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class BurriReplacementDecoderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Recovery/BurriReplacementDecoder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Appendix A objects for a qubit replacement channel.",
        H("A replacement channel and the Schumacher-Westmoreland construction"), Blocks(
            Paragraph(Text("The input is a qubit with reference density diag(2/3,1/3). The channel output space B has dimension one. "
                + "The environment is literally A times B', as prescribed in Appendix A of Burri, arXiv:2502.17411v1. "
                + "The reference purification has correlated amplitudes sqrt(2)/sqrt(3) and 1/sqrt(3). "
                + "The same unit vector is the fixed R'A' ancilla, and W is the identity. The matrix M retains the transpose in Eq. A.6. "
                + "These objects address the actual decoder construction; no lower bound is used as a decoder fidelity.")),
            Entry("psi-normalized", "psi_normalized", "Normalized reference vector",
                "The correlated reference vector has squared norm one.", DescribeRole.Theorem),
            Entry("source-isometry", "source_isometry", "Physical Stinespring isometry",
                "The map from A to B times E is an isometry with E=A times B'. Its environment components are the replacement channel Kraus operators.", DescribeRole.Theorem),
            Entry("source-unitary", "source_unitary", "A unitary on the full source space",
                "The correlated two-dimensional block is [[5,sqrt(2)],[-sqrt(2),5]] divided by 3 sqrt(3). "
                    + "The orthogonal complement is fixed. Both adjoint products are the identity.", DescribeRole.Theorem),
            Entry("source-polar-product", "source_polar_product", "Exact ordered polar product",
                "For X=|psi><psi| and M=(sqrt(Q) X) transposed, the product M U equals X/sqrt(3). "
                    + "This statement retains the source multiplication order.", DescribeRole.Theorem),
            Entry("source-square-root", "source_square_root", "The actual positive square root of X",
                "The rank-one state X is a projection. Its positive square root in the canonical CStarMatrix functional calculus is X itself.", DescribeRole.Theorem),
            Entry("source-polar-positive", "source_polar_positive", "Positivity of the polar product",
                "The ordered product M U is positive semidefinite, since it equals the positive multiple X/sqrt(3).", DescribeRole.Theorem),
            Entry("source-svd", "source_svd", "Singular value decomposition with the specified source action",
                "There are unitary matrices H and T and nonnegative real diagonal entries s such that M=H diag(s) T and U=T adjoint H adjoint. "
                    + "Thus the explicit U arises from an SVD with precisely the Appendix A convention. The proof applies the Hermitian spectral theorem to M U.", DescribeRole.Theorem),
            Entry("source-purification-identity", "source_purification_identity", "The purification identity with a fixed ancilla",
                "For every reference, environment and purifying index, the canonical positive-root amplitude of X agrees with the physical Stinespring purification "
                    + "tensored with the fixed unit ancilla and acted on by W=I. This is the entrywise identity of Eq. A.9 on the full prescribed spaces.", DescribeRole.Theorem),
            Entry("noise-normalization", "noise_normalization", "Replacement-channel Kraus normalization",
                "The Gram sum of the environment components of V is the input identity.", DescribeRole.Theorem),
            Entry("sw-columns", "sw_columns", "Actual composite decoder columns",
                "Composing the source Kraus rows with the ancilla preparation gives two nonzero correlated columns: 2 sqrt(2)/3 and 1/3. "
                    + "These columns are derived from U W and the preparation matrix.", DescribeRole.Theorem),
            Entry("decoder-normalizations", "decoder_normalizations", "Decoder Kraus normalizations",
                "Both the composite source decoder Kraus family and the reference-root times noise-adjoint Kraus family have Gram sum equal to the identity of B.", DescribeRole.Theorem),
            Entry("actual-channels", "actual_channels", "Canonical completely positive trace-preserving maps",
                "Each of the three specified Kraus families is realized by the repository's canonical QuantumChannel interface, with equality of its action and the finite Kraus sum on every input matrix. "
                    + "The comparison of their canonical-purification fidelities and the identification of the reference-root family with the ordinary Petz interface require additional statements.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
