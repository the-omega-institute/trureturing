using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.CorrectedInversion;
internal sealed class SignedSourceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/CorrectedInversion/SignedSource.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed affine source and original finite L1 flow", H("Signed source divided powers"), Blocks(
        Paragraph(Text("For arbitrary original LatticeData D, charge a and finite oscillator polynomial p, affineP(p) is exactly SourceMobius.flowPolynomial applied after the weight-sign algebra map sigma(X(i,r))=(-1)^(r+1)*X(i,r). This is the signed source covariance, not unsigned substitution and not sigma after the flow. No determinant, positive norm or finite-dimensional full weight-space hypothesis is needed in this module.")),
        Paragraph(Text("The proof restores finite polynomial coordinates from the original variable_power and variable_power_charge calculations, reverses the finite binomial range, and compares algebra homomorphisms on generators. SourceMobius supplies the derivation, factorial recurrence and uniform nilpotence. weightSign_monomial and linear extension give sigma(p)=(-1)^R*p on each sourceWeight-homogeneous component. The classical coordinate-change background is FLM; no literature novelty or full VOA/string realization is claimed.")),
        Paragraph(Text("The faithful four-slot escape audit is unfinished under CLAUDE 3.9: https://github.com/the-omega-institute/trureturing/issues/21332. Reg mirrors reconstruct the full source laws, but complete enrolled-template realization, variation, sensitivity, observational dependence and current selector binding are not claimed.")),
        Describe.Lean(DescribeId.Create("original-affine-source-divided-coefficients"), DeclarationHandle.Create(Prefix + "affineP_coeff"),
            H("Exact signed divided powers"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
            Blocks(Paragraph(Text("For p homogeneous of weight R and every natural k, affineP(D,a,p).coeff(k)=(-1)^R times (k!) inverse times sectorL1(D,a)^k(p). The sign is independent of k. This coefficient identity is consumed by actual_corrected_single_inversion."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("original-affine-source-finite-cutoff"), DeclarationHandle.Create(Prefix + "affineP_above_weight"),
            H("Native nilpotence gives the finite cutoff"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
            Blocks(Paragraph(Text("For k>R the same coefficient vanishes. The proof bounds weightedTotalDegree by R, uses the original finite flow expansion and sectorL1_degree_bound, and checks the finite polynomial coefficients. The zero polynomial and rank-zero cases are included. This is consumed when the corrected-field support sum is replaced by range(R+1)."))), DescribeRole.Theorem))));
}
