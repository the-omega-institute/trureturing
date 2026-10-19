using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class OriginalEvenCosineCompleteDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourier normalization and cosine completeness for the original complex AE-even Lebesgue window sector.",
        H("Completeness of the original even cosines"),
        Blocks(
            Paragraph(Text("WindowL2(a) is complex L2 with physical Lebesgue measure on Ioc(-a,a]. originalEven(a) was independently defined by AE reflection invariance of the whole-line indicator zero extension. The analytic comparisons and completeness theorems below require a>0. Fourier indices are integers, cosine indices are natural numbers, and the functions and coefficients remain complex.")),
            Describe.Lean(
                DescribeId.Create("physical-moment"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.moment"),
                H("Unnormalized physical Fourier moment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("character(a,k,x) is Mathlib's Fourier character at the class of x in AddCircle(2*a). moment(a,u,k) integrates character(a,-k,x) times the original zero extension of u over the real line. It is a physical Lebesgue moment, not a normalized probability-measure coefficient. On the original even sector, reflection equates moments at k and -k without conjugating u."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("even-mode-moment"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.even_mode_inner_eq_moment"),
                H("Cosine coefficients of an originally even class"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume a>0 and u belongs to originalEven(a). Pairing the two opposite Fourier characters gives the cosine, so the inner product with modeL2(a,n) is amplitude(a,n) times moment(a,u,n). The natural index n includes zero: the amplitude there is 1/sqrt(2*a), while for n>0 it is 1/sqrt(a). These nonzero amplitudes let vanishing cosine coefficients force vanishing moments."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("interval-coefficient-scale"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.fourierCoeffOn_eq_moment"),
                H("Interval Fourier coefficient normalization"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a>0, arbitrary u and every integer k, fourierCoeffOn on the interval from -a to a equals (2*a)^(-1) times the physical moment. The factor accounts for the entire interval length; physical dx is not silently replaced by normalized Haar measure."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("circle-transport"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.circleTransport"),
                H("Transport to normalized Haar L2"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("With a>0, the Ioc lift gives an L2 class on AddCircle(2*a) for normalized Haar measure. Multiplication by sqrt(2*a) compensates for the dx/Haar mass ratio. The following two theorems record both the norm scale and the coefficient scale of this concrete construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("circle-transport-norm"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.circleTransport_norm_sq"),
                H("The transported squared norm is the physical squared norm"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every u and a>0, the unscaled lift has energy (2*a)^(-1) times the original energy. The square-root multiplier exactly restores the window L2 squared norm, using the original Ioc interval integral and the Haar integration identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("circle-transport-coefficient"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.circleTransport_fourierCoeff"),
                H("The transported Fourier coefficient has the required scale"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a>0 and every integer k, the Fourier coefficient of circleTransport equals sqrt(2*a) times fourierCoeffOn of the original representative. Together with the interval coefficient identity, this is the physical moment divided by sqrt(2*a). Equality of representatives is used almost everywhere on the circle."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("even-cosine-injectivity"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.even_eq_zero_of_mode_inner_eq_zero"),
                H("Vanishing cosine coefficients determine the original even class"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume a>0, u is originally AE-even, and its inner product with every natural cosine mode is zero. The nonzero amplitudes kill all nonnegative Fourier moments, and evenness supplies the negative indices. The proof then applies Mathlib's interval Parseval theorem tsum_sq_fourierCoeffOn directly to the original MemLp representative. All Fourier coefficients zero imply zero physical energy and hence u=0. Completeness is obtained from Parseval, rather than included in the definition of evenness or assumed as a basis hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-even-cosine-closure"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.originalEven_eq_cosineClosure"),
                H("The full original even sector is the closed complex cosine span"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a>0, originalEven(a) equals the topological closure of the complex linear span of all modeL2(a,n). Each mode already lies in the closed original even sector. Conversely, subtracting the orthogonal projection onto cosineClosure from an originally even u leaves an originally even vector orthogonal to every mode; the preceding injectivity theorem makes that residual zero. No finite upper mode cutoff or real-coefficient restriction occurs.")),
                    Paragraph(Text("The argument uses standard Fourier characters, interval Parseval and Hilbert-space projection from Mathlib with explicit measure normalization. It supplies an analytic Hilbert/Fourier identification, with no literature novelty, canonical full Weil arithmetic/operator identification, signed positivity or Riemann-hypothesis conclusion claimed."))),
                DescribeRole.Theorem))));
}
