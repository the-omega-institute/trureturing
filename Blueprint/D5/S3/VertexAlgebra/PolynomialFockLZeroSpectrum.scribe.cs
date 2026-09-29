using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class PolynomialFockLZeroSpectrumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/PolynomialFockLZeroSpectrum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/chulin2018heisenberg");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The concrete polynomial Fock zero mode has finite energy fibers and exact finite-dimensional eigenspaces.",
        H("Polynomial Fock Zero-Mode Spectrum"),
        Blocks(
            Paragraph(Text("The operator is the pointwise finite Sugawara L_0 on the complex "
                + "polynomial Fock space from Polynomial Fock Sugawara Support. A monomial "
                + "has energy equal to the sum of its exponents weighted by variable index "
                + "plus one. The result concerns nonnegative integer eigenvalues; it does "
                + "not construct state fields or a conformal character.")),
            Describe.Lean(
                DescribeId.Create("polynomial-fock-energy-fibers-finite"),
                DeclarationHandle.Create(Prefix + "energyFiber_finite"),
                H("Each weighted-monomial energy fiber is finite"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At energy N, every occupied variable index is below N "
                    + "and each exponent is at most N. Thus exponent vectors of energy N "
                    + "embed in a finite product of finite intervals, including N = 0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("polynomial-fock-zero-mode-eigenspaces"),
                DeclarationHandle.Create(Prefix + "lZero_spectrum"),
                H("The zero-mode eigenspace has the weighted-monomial basis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural N, the kernel of L_0 minus N times "
                    + "the identity is precisely the span of monomials of energy N, and its "
                    + "complex dimension is the number of those monomials. The proof uses "
                    + "the concrete Sugawara-current commutator and coefficient uniqueness; "
                    + "it does not establish the full Virasoro commutator."))),
                DescribeRole.Theorem))));
}
