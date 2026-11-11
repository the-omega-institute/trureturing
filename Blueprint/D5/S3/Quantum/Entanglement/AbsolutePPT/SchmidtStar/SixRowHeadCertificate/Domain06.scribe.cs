using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate;
internal sealed class Domain06Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "This subtree proves the scalar polynomial nonnegative on its stated feasible subdomain. Exact midpoint splits cover their boundary faces; excluded boxes contradict the nonnegative feasibility constraint. Its root is consumed by the complete domain partition.", H("Domain06"), Blocks(
            Paragraph(Text("This subtree proves the scalar polynomial nonnegative on its stated feasible subdomain. Exact midpoint splits cover their boundary faces; excluded boxes contradict the nonnegative feasibility constraint. Its root is consumed by the complete domain partition.")),
            Describe.Lean(DescribeId.Create("sixrowheadcertificate-domain06-node384"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Domain06.node384"),
                H("Feasible subtree"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem node384 (z k h : ℝ)     (hz : (3 / 8) ≤ z) (hZ : z ≤ (3 / 4))     (hk : 0 ≤ k) (hK : k ≤ 1)     (hh : (3 / 4) ≤ h) (hH : h ≤ (3 / 2))     (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h"))), DescribeRole.Theorem)
        )));
}
