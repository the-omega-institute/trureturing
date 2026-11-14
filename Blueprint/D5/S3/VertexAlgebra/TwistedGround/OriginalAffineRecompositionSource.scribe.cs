using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalAffineRecompositionSourceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/OriginalAffineRecompositionSource.";
    private static readonly LibraryNoteRef Background = LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete original corrected Gaussian Laurent row", H("Complete original corrected Gaussian Laurent row"),
        Blocks(
            Paragraph(Text("These are finite algebraic identities on the original lattice oscillator carrier. No positivity, analytic convergence, frequency cutoff or charge truncation is assumed. The determinant-unit hypothesis is retained exactly where the original normal and corrected operators require it.")),
            Describe.Lean(DescribeId.Create("original-affine-recomposition-source-recompositionamplitude-eq"), DeclarationHandle.Create(Prefix + "recompositionAmplitude_eq"), H("recompositionAmplitude_eq"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Background), Blocks(Paragraph(Text("For arbitrary finite labels and all three occupations, the finite residual contraction equals the source factorial times the ordinary affine coefficient of correctedMatrix and correctedMean."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-affine-recomposition-source-original-corrected-gaussian-row"), DeclarationHandle.Create(Prefix + "original_corrected_gaussian_row"), H("original_corrected_gaussian_row"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Background), Blocks(Paragraph(Text("For every lattice data D with IsUnit(D.G.det), arbitrary charge a, all original occupations alpha, beta and gamma, and every integer e, wick of monomial(gamma,1) against oscillatorCorrected(D,hu,a,e,monomial(alpha,1),monomial(beta,1)) equals weight(alpha) weight(beta) weight(gamma) times the affine Laurent coefficient of correctedMatrix and correctedMean on exactly the support union at e+chargeNorm(a). The empty union is included; no extra support, recurrence or recomposition equation is a premise."))), DescribeRole.Theorem),
            Paragraph(Text("The proof homogenizes both affine kernels, derives the exact auxiliary Z Y factor by native Gaussian insertion and induction, and applies ElementaryGaussianContraction.coefficient_contraction with its proved support bounds. Shared auxiliary factorial cancellation precedes bounded finite-sum reindexing. Explicit embeddings transport the effective kernel back to the original corrected kernel. The auxiliary factorization identifies the shared contraction with the corrected source/source block and source mean.")),
            Paragraph(Text("Attribution: finite Gaussian/Wick calculus and factorial Fock normalization are classical. The lattice and twisted-current suppliers retain their FLM, Dong--Nagatomo and Bakalov--Kac attributions. The exact composition on the original repository carrier is repo-derived; no external novelty is asserted. The bibliographic background does not supply an uninspected theorem or replace these proofs.")),
            Paragraph(Text("The downstream original identityK and two-row sewing remain open, with all four external factorials, both chargeScalar factors, one left average and the original inverse -Ginv/(k+1). These row identities do not establish VOA or Jacobi axioms, crossing, Monster, CFT, BRST, string dynamics or a physical realization."))), []));
}
