using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate;
internal sealed class Domain03Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "This subtree proves the scalar polynomial nonnegative on its stated feasible subdomain. Exact midpoint splits cover their boundary faces; excluded boxes contradict the nonnegative feasibility constraint. Its root is consumed by the complete domain partition.", H("Domain03"), Blocks(
            Paragraph(Text("This subtree proves the scalar polynomial nonnegative on its stated feasible subdomain. Exact midpoint splits cover their boundary faces; excluded boxes contradict the nonnegative feasibility constraint. Its root is consumed by the complete domain partition.")),
            Describe.Lean(DescribeId.Create("sixrowheadcertificate-domain03-node325"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Domain03.node325"),
                H("Feasible subtree"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem node325 (z k h : ℝ)     (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))     (hk : (3 / 4) ≤ k) (hK : k ≤ 1)     (hh : (3 / 8) ≤ h) (hH : h ≤ (3 / 4))     (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h"))), DescribeRole.Theorem)
        )));
}
