using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalChargedRowSourceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/OriginalChargedRowSource.";
    private static readonly LibraryNoteRef Background = LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Charged correction and signed current suppliers", H("Charged correction and signed current suppliers"),
        Blocks(
            Paragraph(Text("These are finite algebraic identities on the original lattice oscillator carrier. No positivity, analytic convergence, frequency cutoff or charge truncation is assumed. The determinant-unit hypothesis is retained exactly where the original normal and corrected operators require it.")),
            Describe.Lean(DescribeId.Create("original-charged-row-source-affinekernel"), DeclarationHandle.Create(Prefix + "affineKernel"), H("affineKernel"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Background), Blocks(Paragraph(Text("The homogenized quadratic has blocks A, mu, transpose(mu), and zero on one auxiliary coordinate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-charged-row-source-affinecoefficient"), DeclarationHandle.Create(Prefix + "affineCoefficient"), H("affineCoefficient"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Background), Blocks(Paragraph(Text("The ordinary coefficient of the finite affine Gaussian exponential is the sum of native homogeneous coefficients over auxiliary degrees zero through the occupation degree."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-charged-row-source-chargedcorr-linearforms"), DeclarationHandle.Create(Prefix + "chargedCorr_linearForms"), H("chargedCorr_linearForms"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Background), Blocks(Paragraph(Text("For arbitrary lattice data D, charge a, complex z, residual coordinate evaluation x, finite family c of actual oscillator linear forms and every occupation d, chargedReadout of the product equals weight(d) times the affine coefficient. The covariance is the original pairScalar times Gram times z to the sum of source frequencies. The mean retains every residual coordinate x and the charged singleton; no neutral-charge substitution is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-charged-row-source-wick-flat-cons"), DeclarationHandle.Create(Prefix + "wick_flat_cons"), H("wick_flat_cons"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Background), Blocks(Paragraph(Text("The original all-signed flat-current recursion has coefficient minus (k+1) times choose(-m-1/2,k+1). A negative mode differentiates the detector; a nonnegative mode differentiates the input. Both branches retain the original doubled exponent shift."))), DescribeRole.Theorem),
            Paragraph(Text("The noncentral moment comparison uses strong induction on occupation degree after deriving the original insertion law. The auxiliary coefficient and affine-moment identities also supply the normal and corrected-row calculations.")),
            Paragraph(Text("Attribution: finite Gaussian/Wick calculus and factorial Fock normalization are classical. The lattice and twisted-current suppliers retain their FLM, Dong--Nagatomo and Bakalov--Kac attributions. The exact composition on the original repository carrier is repo-derived; no external novelty is asserted. The bibliographic background does not supply an uninspected theorem or replace these proofs.")),
            Paragraph(Text("The downstream original identityK and two-row sewing remain open, with all four external factorials, both chargeScalar factors, one left average and the original inverse -Ginv/(k+1). These row identities do not establish VOA or Jacobi axioms, crossing, Monster, CFT, BRST, string dynamics or a physical realization."))), []));
}
