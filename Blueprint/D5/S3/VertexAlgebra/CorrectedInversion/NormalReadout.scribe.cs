using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.CorrectedInversion;
internal sealed class NormalReadoutDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/CorrectedInversion/NormalReadout.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original normal transpose in finite polynomial coordinates", H("Normal reflection readout"), Blocks(
        Paragraph(Text("The source algebra, actual tensor module and original bilinear actualForm are unchanged. D is arbitrary LatticeData; the scalar transpose uses hu:IsUnit(D.G.det), arbitrary signed charge norm and coefficient index e, and arbitrary actual tensors x,y. There is no ground symmetry, positivity, finite-dimensional full weight space or representability hypothesis. This is the classical bilinear coordinate-change setting of FLM, with no literature novelty claim.")),
        Paragraph(Text("normalP is optionEquivLeft composed with the original normalReflection and embed from ActualCorrCovariance. affineP is the same polynomial-coordinate conversion of its affineSource; it is not corrLift. The dependent JetTuple expansion retains repeated source occurrences. The proof uses the original actual_polynomial_monomial_transpose and identifies its exponent as shiftIndex(D,a,R,j)-e, with shiftIndex=-2*chargeNorm(D,a)-4*R+2*j. Linear extension through the existing monomial basis then handles every homogeneous polynomial, including zero.")),
        Paragraph(Text("The faithful four-slot escape audit is unfinished under CLAUDE 3.9: https://github.com/the-omega-institute/trureturing/issues/21332. Reg mirrors reconstruct the full source laws, but complete enrolled-template realization, variation, sensitivity, observational dependence and current selector binding are not claimed.")),
        Describe.Lean(DescribeId.Create("original-normal-generator-coordinates"), DeclarationHandle.Create(Prefix + "normalP_X"),
            H("Signed triangular generator coordinates"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
            Blocks(Paragraph(Text("For i=(b,r), normalP(X i) is the sum for s:Fin(r+1) of the degree r-s monomial with coefficient (-1)^(r+1)*choose(r+1,s+1) times X(b,s). This coordinate helper is consumed by the dependent word-product expansion and the signed native-flow identification."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("original-normal-homogeneous-readout"), DeclarationHandle.Create(Prefix + "normal_homogeneous_readout"),
            H("Original homogeneous normal scalar transpose"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
            Blocks(Paragraph(Text("For sourceWeight-homogeneous p of weight R, the original left polynomialField coefficient paired with y equals paritySign(chargeNorm(a)/2) times ActualCorrCovariance.scalarReadout of normalP(p), using the original right form orientation and coefficient shiftIndex(D,a,R,j)-e in readout j. The finite dependent product identity normalP_word lies on the proof path. No desired normal covariance is assumed."))), DescribeRole.Theorem))));
}
