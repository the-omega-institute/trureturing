using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class BurriReplacementDecoderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Recovery/BurriReplacementDecoder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Appendix A replacement-channel decoders and their strict squared-fidelity comparison.",
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
                "For X=|psi><psi| and the displayed diagonal matrix sqrtQ, set M=(sqrtQ X) transposed. The product M U equals X/sqrt(3). "
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
                    + "The following statements identify the physical marginals and ordinary Petz recovery and evaluate the overlap for the actual composite maps.", DescribeRole.Theorem),
            Entry("physical-marginals", "physical_marginals", "Marginals of the physical Stinespring purification",
                "The RBE pure density is constructed from the canonical reference vector and V. Its RE marginal is X, its R marginal is rho, "
                    + "and its E marginal is diag(2/3,1/3) in the full source environment coordinates.", DescribeRole.Theorem),
            Entry("reference-root", "reference_root", "Positive reference square root",
                "The functional-calculus positive square root of rho is the diagonal matrix with entries sqrt(2)/sqrt(3) and 1/sqrt(3).", DescribeRole.Theorem),
            Entry("product-marginal-root", "product_marginal_root", "Positive root of the actual product marginals",
                "The displayed matrix sqrtQ is the unique positive square root of rho tensor sigmaE, where both factors are proved physical marginals.", DescribeRole.Theorem),
            Entry("ordinary-petz-channel", "ordinary_petz_channel", "The ordinary Petz channel with zero completion defect",
                "The noise output of rho is the identity on Fin 1 and is positive definite. Its spectral support and inverse positive square root are both the identity. "
                    + "The displayed petzKraus are therefore exactly the ordinary Petz Kraus factors. The reference-state completion theorem supplies the canonical CPTP map, "
                    + "and its complementary reset term vanishes on every input matrix.", DescribeRole.Theorem),
            Entry("canonical-reference-amplitude", "canonical_reference_amplitude", "Canonical purification amplitude",
                "The reference vector is entrywise the positive square root of the nonuniform density rho.", DescribeRole.Theorem),
            Entry("actual-recovered-purifications", "actual_recovered_purifications", "Actual recovered reference-output densities",
                "The reference tensor extension of the actual Petz-after-noise channel sends the canonical pure reference density to rho tensor rho. "
                    + "The actual Appendix A SW-after-noise channel sends it to rho tensor diag(8/9,1/9). These identities precede the fidelity calculation.", DescribeRole.Theorem),
            Entry("actual-strict-fidelity", "actual_strict_fidelity", "SW strictly beats ordinary Petz for this physical channel",
                "The squared pure-reference overlap of the actual Petz composite is 1/3, and that of the actual source SW composite is 11/27. "
                    + "Their difference is 2/27, so the SW fidelity is strictly larger. Fidelity is defined by the actual recovered density's overlap with the canonical reference vector, "
                    + "rather than by a reduced target formula. This is the replacement-channel direction of Burri's Question 1 only; the opposite direction and the full no-order conclusion are not asserted.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
