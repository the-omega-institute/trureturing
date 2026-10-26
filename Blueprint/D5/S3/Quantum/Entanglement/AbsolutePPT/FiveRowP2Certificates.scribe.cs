using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;
internal sealed class FiveRowP2CertificatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact rational polynomial identities certify the upper and small-tail branches of the five-row scalar relaxation. Every coefficient and inequality is a real algebraic statement.", H("FiveRowP2Certificates"), Blocks(
            Paragraph(Text("Exact rational polynomial identities certify the upper and small-tail branches of the five-row scalar relaxation. Every coefficient and inequality is a real algebraic statement.")),
            Describe.Lean(DescribeId.Create("fiverowp2certificates-upper-certificate"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Certificates.upper_certificate"),
                H("upper certificate"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem upper_certificate {r H D a q s : ℝ} (h : Hyp r H D a q s) (hr : 1/5 ≤ r) : W r H D a q ≤ B r"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fiverowp2certificates-smallq-certificate"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Certificates.smallq_certificate"),
                H("smallq certificate"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem smallq_certificate {r H D a q s : ℝ} (h : Hyp r H D a q s) (hr : 1/12 ≤ r) (hr' : r ≤ 1/5) (hq : q ≤ 1) : W r H D a q ≤ B r"))), DescribeRole.Theorem)
        )));
}
