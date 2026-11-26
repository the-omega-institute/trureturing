using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class ThirdTwistedScalarLocalityDocument : IScribeDocumentDefinition
{
    private const string Orbifold = "D5/S3/VertexAlgebra/Lattice/Orbifold/";
    private const string Prefix = Orbifold + "ThirdTwistedScalarLocality.";
    private static readonly LibraryNoteRef TwistedLattice =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The order-three contraction clears to one finite homogeneous numerator in rational and formal expansions.",
        H("Order-Three Scalar Contraction Clearing"),
        Blocks(
            Paragraph(Text("For the cover coordinates x = z^(1/3) and y = w^(1/3), use the ratio "
                + "t = y/x in the binomial product of Bakalov–Kac, arXiv:math/0402315v3, §4, "
                + "Lemma 4.2, equation (4.34). Let D be the lattice, g an additive equivalence "
                + "of its charges, and u a primitive cubic root when factoring x³ − y³. "
                + "The three orbit pairings may have either sign.")),
            Describe.Lean(
                DescribeId.Create("third-twisted-orbit-exponent"),
                DeclarationHandle.Create(Prefix + "contractionOrbitExponent"),
                H("Integral orbit pairing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedLattice),
                Blocks(Paragraph(Text("The exponent eⱼ for charges a and b is the integral "
                    + "pairing ⟨gʲa,b⟩."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("third-twisted-clearing-order"),
                DeclarationHandle.Create(Prefix + "contractionLocalityOrder"),
                H("Clearing order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedLattice),
                Blocks(Paragraph(Text("Take the maximum of the three negative parts max(0, −eⱼ) "
                    + "for j = 0, 1, 2."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("third-twisted-clearing-order-sufficient"),
                DeclarationHandle.Create(Prefix + "contractionLocalityOrder_add_nonneg"),
                H("Nonnegative cleared exponents"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedLattice),
                Blocks(Paragraph(Text("At the clearing order N, each N + eⱼ with j = 0, 1, 2 "
                    + "is nonnegative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-twisted-cleared-numerator"),
                DeclarationHandle.Create(Prefix + "clearedContractionNumerator"),
                H("Two-variable numerator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedLattice),
                Blocks(Paragraph(Text("For any complex unit u and natural order N, form the "
                    + "product of the three linear polynomials x − uʲy to the natural powers "
                    + "max(0, N + eⱼ). When every N + eⱼ is nonnegative, the exponents are exactly "
                    + "N + eⱼ and the product is homogeneous of degree 3N + ∑ⱼ eⱼ."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("third-twisted-cleared-numerator-evaluation"),
                DeclarationHandle.Create(Prefix + "clearedContractionNumerator_eval"),
                H("Evaluation of the numerator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedLattice),
                Blocks(Paragraph(Text("For a coefficient map C from ℂ into a commutative ring, "
                    + "evaluation at x and y gives the product of x − C(uʲ)y to the natural "
                    + "powers max(0, N + eⱼ)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-twisted-rational-homogeneous-clearing"),
                DeclarationHandle.Create(Prefix + "rationalContraction_clear_homogeneous"),
                H("Homogeneous rational clearing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedLattice),
                Blocks(Paragraph(Text("For rational functions x and y with x ≠ 0 and x³ − y³ ≠ 0, "
                    + "the rational contraction at y/x is multiplied by the orbit monomial "
                    + "x^(∑ⱼ eⱼ) and by (x³ − y³)^N. The result is the evaluation of the "
                    + "two-variable numerator whenever u is primitive of order three and every "
                    + "N + eⱼ is nonnegative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-twisted-cleared-taylor-polynomial"),
                DeclarationHandle.Create(Prefix + "clearedContractionTaylorPolynomial"),
                H("Numerator in the ratio coordinate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedLattice),
                Blocks(Paragraph(Text("Evaluate the two-variable numerator at x = 1 and y = X "
                    + "to obtain a polynomial in the ratio coordinate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("third-twisted-binomial-homogeneous-clearing"),
                DeclarationHandle.Create(Prefix + "binomialContraction_clear_homogeneous"),
                H("Homogeneous clearing after formal expansion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedLattice),
                Blocks(Paragraph(Text("Let F map complex formal power series into a commutative "
                    + "ring, let x be a unit there, and put y = x F(X). For a primitive cubic "
                    + "root u and an order N with every N + eⱼ nonnegative, multiply the image "
                    + "under F of the binomial units to their integer powers eⱼ by the unit monomial "
                    + "x^(∑ⱼ eⱼ) and by (x³ − y³)^N. This gives the same polynomial evaluated "
                    + "at x and y with coefficient map F ∘ C, where C includes the complex "
                    + "constants as power series."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-twisted-scalar-clearing-at-indeterminate"),
                DeclarationHandle.Create(Prefix + "scalar_contraction_X_clear"),
                H("Clearing the scalar contraction at X"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedLattice),
                Blocks(Paragraph(Text("At the Bakalov–Kac root ζ, multiply the scalar contraction "
                    + "exponential by (1 − X³)^N. The result is the ratio-coordinate polynomial "
                    + "viewed as a power series whenever every N + eⱼ is nonnegative. The "
                    + "rational product and the scalar exponential agree through the Laurent "
                    + "expansion at X."))),
                DescribeRole.Theorem))));
}
