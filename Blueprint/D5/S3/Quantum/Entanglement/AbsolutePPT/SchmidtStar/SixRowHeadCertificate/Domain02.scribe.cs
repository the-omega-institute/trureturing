using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate;
internal sealed class Domain02Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "This subtree proves the scalar polynomial nonnegative on its stated feasible subdomain. Exact midpoint splits cover their boundary faces; excluded boxes contradict the nonnegative feasibility constraint. Its root is consumed by the complete domain partition.", H("Domain02"), Blocks(
            Paragraph(Text("This subtree proves the scalar polynomial nonnegative on its stated feasible subdomain. Exact midpoint splits cover their boundary faces; excluded boxes contradict the nonnegative feasibility constraint. Its root is consumed by the complete domain partition.")),
            Describe.Lean(DescribeId.Create("sixrowheadcertificate-domain02-node84"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Domain02.node84"),
                H("Feasible subtree"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem node84 (z k h : ℝ)     (hz : (9 / 16) ≤ z) (hZ : z ≤ (21 / 32))     (hk : (1 / 2) ≤ k) (hK : k ≤ (3 / 4))     (hh : 0 ≤ h) (hH : h ≤ (3 / 8))     (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h"))), DescribeRole.Theorem)
        )));
}
