using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.ComplementaryCorrelations;

internal sealed class AnchorMUBNormalFormTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local-unitary covariance of the actual anchor form.",
        H("Local-unitary covariance of the actual anchor form"),
        Blocks(
            Describe.Lean(DescribeId.Create("qian-anchormubnormalformtransport-logderiv-inbasis"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalFormTransport.logDeriv_inBasis"),
                H("Resolvent derivative covariance"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Unitary conjugation commutes with each shifted inverse and hence with the integrated log resolvent derivative."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("qian-anchormubnormalformtransport-marginalfree-inbasis"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalFormTransport.marginalFree_inBasis"),
                H("Preservation of the tangent conditions"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Local conjugation preserves Hermiticity. Each partial trace transforms by conjugation on its remaining subsystem and therefore stays zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("qian-anchormubnormalformtransport-anchorquadraticin-normalform"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalFormTransport.anchorQuadraticIn_normalForm"),
                H("Transfer of the entire quadratic"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Local conjugation transports the product density and tangent. Relabeling and rephasing outcomes preserve the two Fisher sums, and trace invariance preserves the BKM term."))), DescribeRole.Theorem))));
}
