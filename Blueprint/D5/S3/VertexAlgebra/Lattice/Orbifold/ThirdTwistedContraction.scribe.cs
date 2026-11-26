using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class ThirdTwistedContractionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContraction.";
    private static readonly LibraryNoteRef TwistedLattice =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized scalar contraction and its complementary Fourier coefficient for a cubic lattice twist.",
        H("Order-Three Twisted Lattice Contraction"),
        Blocks(
            Paragraph(Text("Let D be the native even integral lattice and g an additive equivalence of its charges. "
                + "Write ⟨a,b⟩ for the lattice pairing and extend it complex bilinearly using D's Gram matrix.")),
            Describe.Lean(
                DescribeId.Create("third-twisted-scalar-contraction"),
                DeclarationHandle.Create(Prefix + "scalar_contraction"),
                H("The normalized scalar product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(TwistedLattice),
                Blocks(Paragraph(Text("In Lemma 4.2, equation (4.34) of arXiv:math/0402315v3, factor out the "
                    + "powers of z and put X = (w/z)^(1/3). The normalized factor is the product of "
                    + "(1 − ζʲX) raised to ⟨gʲa,b⟩ for j = 0, 1, 2. These are integer powers of units "
                    + "in the power-series ring. The product equals the formal exponential of the series "
                    + "with constant term zero and degree-n coefficient −Σⱼ ⟨gʲa,b⟩ζ^(jn)/n for n > 0. "
                    + "The Lean identity holds for any complex ζ."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-twisted-complementary-coefficient"),
                DeclarationHandle.Create(Prefix + "coeff_contractionExponent_opposite"),
                H("Pairing the complementary Fourier components"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedLattice),
                Blocks(Paragraph(Text("Assume g³ = 1, g preserves the pairing, and ζ³ = 1. For n > 0 put "
                    + "u = ζ^(n mod 3) and Pᵤ(a) = (a + u g a + u² g² a)/3 in the complexified lattice. "
                    + "The degree-n coefficient of the exponent is −⟨Pᵤ(a), P_(u²)(b)⟩/(n/3). "
                    + "The two components have "
                    + "eigenvalues u⁻¹ and u under the complex extension of g."))),
                DescribeRole.Theorem))));
}
