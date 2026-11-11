using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar;
internal sealed class SixRowHeadCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A binary midpoint partition covers the complete scalar box, including every boundary face. Its 119 positive leaves use exact homogeneous Bernstein identities. Its 99 excluded leaves have a strictly negative upper bound for the feasibility polynomial. The polynomial is therefore nonnegative at every feasible point.", H("SixRowHeadCertificate"), Blocks(
            Paragraph(Text("A binary midpoint partition covers the complete scalar box, including every boundary face. Its 119 positive leaves use exact homogeneous Bernstein identities. Its 99 excluded leaves have a strictly negative upper bound for the feasibility polynomial. The polynomial is therefore nonnegative at every feasible point.")),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadcertificate-polynomial-nonneg"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate.polynomial_nonneg"),
                H("polynomial nonneg"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem polynomial_nonneg (z k h : ℝ) (hz : 0 ≤ z) (hZ : z ≤ 3/4) (hk : 0 ≤ k) (hK : k ≤ 1) (hh : 0 ≤ h) (hH : h ≤ 3/2) (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h"))), DescribeRole.Theorem)
        )));
}
