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
                    + "This statement retains the source multiplication order.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
