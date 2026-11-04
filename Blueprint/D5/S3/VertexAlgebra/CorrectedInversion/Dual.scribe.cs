using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.CorrectedInversion;
internal sealed class DualDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/CorrectedInversion/Dual.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite original-source functional-dual inversion", H("Original finite dual identity"), Blocks(
        Paragraph(Text("coordinateInversion is a Complex-linear map from the original Carrier D to integer-indexed finite Carrier families. On the original monomial single(a,m), let R=weight(sourceWeight,m), N=chargeNorm(D,a) and d_j=-2N-4R+2j. Its value is the sum for j=0..R of the Finsupp singleton at d_j with vector paritySign(N/2)*(-1)^R/j! times (sugawaraMode D (LatticeSugawaraCurrents.gramComplex D)^(-1) 1)^j applied to that original source. It is extended through the existing oscillator monomial basis and finite charge direct sum. Finsupp addition merges all coincident integer shifts and permits cancellation.")),
        Paragraph(Text("K_L is exactly the existing correctedDualCoefficient from TwistedGround.CorrectedDualCoefficient. K_R(e)(v)=actualForm(D,hu,x,Ycorr(v).coeff(e)y) keeps the distinct original right orientation. The proof uses the original integer determinant-unit assumption to identify the actual inverse-Gram Sugawara powers with SourceMobius.sectorL1 powers, consumes actual_corrected_monomial_inversion, and proves equality of linear functionals on the existing monomial/charge basis.")),
        Paragraph(Text("Only the transformed input v has finite coefficient support. The theorem makes no claim of finite charge support for a fixed dual functional, graded restricted-dual membership, representability, positivity, form symmetry or Hermitian adjointness. It does not establish the full Monster/VOA/fusion/string/AdS-CFT objective. The coordinate-change background is classical FLM, with no literature novelty claim.")),
        Paragraph(Text("The faithful four-slot escape audit is unfinished under CLAUDE 3.9: https://github.com/the-omega-institute/trureturing/issues/21332. Reg mirrors reconstruct the full source laws, but complete enrolled-template realization, variation, sensitivity, observational dependence and current selector binding are not claimed.")),
        Describe.Lean(DescribeId.Create("original-finite-functional-dual-inversion"), DeclarationHandle.Create(Prefix + "actual_dual_inversion"),
            H("Actual finite functional-dual identity"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
            Blocks(Paragraph(Text("For every original Carrier source v, arbitrary signed e and arbitrary actual tensors x,y under the original hu, K_L(e)(v) is the sum over d in the actual support of coordinateInversion(v) of K_R(d-e)(coordinateInversion(v)(d)). This is an actual finite coefficient sum. No injectivity of shifts, unique charge decomposition beyond the existing Finsupp, desired inversion law or representability premise is assumed."))), DescribeRole.Theorem))));
}
