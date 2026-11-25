using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Marginals;

internal sealed class RationalQubitEqualSpectrumRankDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rational rank bound for qubit marginals with equal spectra.",
        H("Rational extensions of rank at most two for equal spectra"),
        Blocks(
            Describe.Lean(DescribeId.Create("rational-qubit-equal-spectrum-rank"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Entanglement/Marginals/RationalQubitEqualSpectrumRank."
                    + "rational_endpoint_rank_le_two_of_equal_det"),
                H("A rational joint state of rank at most two for equal determinants"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two positive semidefinite trace-one qubit marginals with rational real and "
                    + "imaginary parts and equal determinants admit a positive semidefinite joint "
                    + "matrix of rank at most two with rational real and imaginary parts.")),
                    Paragraph(Text(
                    "Subtract half the identity from each marginal. The two centered "
                    + "matrices square to the same scalar times the identity. If the scalar "
                    + "is nonzero, divide their tensor product by it to obtain a traceless "
                    + "Hermitian involution. The projection onto its positive eigenspace "
                    + "has trace and rank two. Compress the left marginal tensored with "
                    + "the identity by this projection. The centered traces vanish, while "
                    + "the trace of the left marginal times its centered part is twice "
                    + "the common scalar. The two partial traces recover the given marginals. "
                    + "If the scalar is zero, both marginals are half the identity. The "
                    + "equal mixture of the two matching basis words gives the required state."))),
                DescribeRole.Theorem))));
}
