using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class CirculantCharpolyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/CirculantCharpoly";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourier modes factor the characteristic polynomial of a circulant matrix.",
        H("Circulants and paired real cosine modes"), Blocks(
            Item("root", "A positive primitive root", "For positive n, the complex exponential exp(2 pi i/n) is primitive and fixes the positive orientation of the modes.", DescribeRole.Definition),
            Item("fourierValue", "Complex mode values", "The value at mode j is the sum of v(k) times the primitive root to the natural power j k.", DescribeRole.Definition),
            Item("fourierVector", "Fourier vectors", "The vector at mode j has coordinate exp(-2 pi i j k/n). Mathlib defines a circulant entry by v(a-b), so this negative vector exponent corresponds to a positive eigenvalue exponent.", DescribeRole.Definition),
            Item("fourierBasis", "An invertible Fourier basis", "Transport the coordinate basis through the invertible discrete Fourier transform, then identify the finite residue indices with Fin n. No primality assumption on n is needed.", DescribeRole.Definition),
            Item("circulant_mulVec_fourier", "The Fourier eigenvector equation", "Multiplication of a circulant by a Fourier vector gives that vector multiplied by its positive-exponent Fourier value. Reflecting the generating vector in the discrete Fourier diagonalization proves the equation.", DescribeRole.Theorem),
            Item("circulant_charpoly", "The complex characteristic polynomial", "For every positive order n and arbitrary complex generating vector v, the characteristic polynomial is the product over all Fourier modes of X minus the mode value. The invertible discrete Fourier transform supplies a basis of Fourier vectors. The eigenvector equations give a diagonal matrix in that basis, so the product includes all algebraic multiplicities.", DescribeRole.Theorem),
            Item("realCirculant", "Real residue entries", "For order 2m+1 and f on the natural numbers, the entry at a,b is f evaluated at the least nonnegative residue of a-b. Values of f outside this residue range are irrelevant.", DescribeRole.Definition),
            Item("cosineValue", "Real cosine mode values", "The real mode indexed by j is f(0) plus twice the sum from l=1 to m of f(l) cos(2 pi j l/(2m+1)).", DescribeRole.Definition),
            Item("realCirculant_charpoly", "One constant factor and squared cosine factors", "Assume f(2m+1-k)=f(k) for each k from 1 to 2m. The characteristic polynomial equals the constant-mode linear factor times the product of the squared linear factors of modes 1 through m. Pairing a residue with its negative gives the cosine formula, and pairing opposite mode indices gives the squares. Injectivity of real-to-complex polynomial mapping transfers the complex identity to real coefficients. The statement includes m=0 and allows coincident mode values.", DescribeRole.Theorem))));

    private static DocumentBlock Item(string name, string title, string explanation, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("circulant-charpoly-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), role);
}
