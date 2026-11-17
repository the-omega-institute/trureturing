using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianFixedEnergyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFixedEnergy.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "OriginalGaussianFixedEnergy", H("Exact original fixed-energy coefficient"), Blocks(
            Paragraph(Text("The original energy-n Wick finsum equals the ordinary coefficient of order 2*n of the literal limiting sewn Gaussian. The proof combines the compact four-support common-box identity, justified fixed external extraction, finite source energy stabilization and the existing locally uniform cutoff coefficient limit. Both charge scalars, four external factorials, exactly one internal factorial and both literal integer Laurent selectors are retained. The limiting Gaussian uses the full chargeNorm times sourceConstant, including its inverse frequency, and the original effective kernel and opposite-charge means. There is no charge averaging, reflection, extra half, source evaluation at one, identity-kernel hypothesis or assumed target identity. The theorem includes energy zero, rank zero, empty supports and zero finite cutoffs in the analytic suppliers. This coefficient identity is a mathematical bridge and does not establish the full Moonshine, VOA, CFT, string-theory or AdS/CFT scientific objective.")),
            N("original_fixed_energy_coefficient", "Exact original terminal coefficient", "The literal original energy finsum, including both selectors and every factorial and charge factor, is identified with the twice-energy ordinary coefficient of the actual explicit sewn limit.", DescribeRole.Theorem)), []));

    private static DocumentBlock N(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("original-fixed-energy-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
