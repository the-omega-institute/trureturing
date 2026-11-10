using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeCosetTransverseDocument : IScribeDocumentDefinition
{
    private static DocumentBlock D(string selector, string text, DescribeRole role) => Describe.Lean(
        DescribeId.Create("coset-transverse-" + selector.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeCosetTransverse." + selector),
        H(selector), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LatticeCosetTransverse", H("Native transverse oscillator contraction"), Blocks(
            D("transverse", "For every external coordinate j and natural frequency k, the actual ambient polynomial X(new j,k) minus the sum over old i of (HB)(i,j) times X(old i,k). The original D has arbitrary finite rank and the external block has arbitrary finite rank.", DescribeRole.Definition),
            D("transversePair", "For arbitrary integral external a and coordinate j, sum over k of a(k) times the (k,j) entry of C minus B transpose H B, calculated rationally.", DescribeRole.Definition),
            D("translatedProjection", "Apply the actual native translatedPolynomial associated to an arbitrary ambient charge A, then apply polynomialProjection to every polynomial coefficient. This is an algebra homomorphism into the original oscillator-polynomial ring with one formal translation variable.", DescribeRole.Definition),
            D("transverse_translation", "Assume only that the original Gram matrix is positive definite. For every external integral a, original integral n, external j and natural oscillator index k, translatedProjection at charge (n,a), on transverse(j,k), is minus the constant polynomial of transversePair(a,j) times X^(k+1). The old charge cancels using G HB=B. The sign is the minus sign in the original translationVariable; ambient positivity is not assumed.", DescribeRole.Theorem),
            D("longitudinalTranslation", "On arbitrary ambient polynomials, first apply polynomialProjection, then translate each old oscillator using the actual ambient pairing of its old unit vector with the given ambient charge A. It differs from translatedProjection because projection precedes translation.", DescribeRole.Definition),
            D("creationSeries_difference", "For every positive definite original D, arbitrary integral B and symmetric even-diagonal C, external a,b and original n,m, map the actual creationSeries of charge (m,b) by translatedProjection at (n,a), and subtract its map by longitudinalTranslation at (n,a). The q-th coefficient is zero at q=0, and otherwise minus q inverse times the constant polynomial of schur(a,b), times X^q. This identifies the entire logarithmic defect, including all oscillator frequencies, directly on the native creationSeries.", DescribeRole.Theorem),
            D("creationExponential_factorization", "For every positive definite original D of arbitrary finite rank, arbitrary finite external rank, integral B, symmetric even-diagonal C, external a,b and original n,m, map the complete native creationExponential at (m,b) by translatedProjection at (n,a). The result equals its map by longitudinalTranslation at (n,a), multiplied by the rational binomial series of schur(a,b), rescaled by minus the polynomial variable. Its j-th scalar coefficient is (-1)^j choose(schur(a,b),j). Both ranks may be zero; the ambient block form need not be positive. The coefficient differential equation follows from creationSeries_difference and the native exponential derivative, and native coefficient uniqueness identifies the entire series.", DescribeRole.Theorem),
            Paragraph(Text("Bakalov-Kac, math/0402315v1, section 4.1, supplies the native exponential and annihilation conventions; imported residue suppliers retain their Carnahan Apache-2.0 attribution. The native polynomial translation defect and its complete exponential Schur factor are calculated here. The downstream LatticeCosetOperatorCorrection consumes these coefficients in the full all-state intermediate-projection identity. Fusion-category descent and analytic sewing are outside this statement.")))));
}
