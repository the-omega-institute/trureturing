using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class ThirdTwistedQuadraticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedQuadratic.";
    private static readonly LibraryNoteRef TwistedProducts =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fractional Virasoro modes are the ordered quadratic coefficients of the two complementary currents, with the vacuum shift.",
        H("The Ordered Quadratic of the Third Cover"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("third-twisted-quadratic-ordered-pair"),
                DeclarationHandle.Create(Prefix + "orderedPair"),
                H("Sign ordering of the current modes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedProducts),
                Blocks(Paragraph(Text("Let k and l be native indices, with frequencies k/3 and l/3. "
                    + "Place the first current on the left when k is negative and on the right otherwise. "
                    + "This is the mode ordering of the field product at n = −1 in Bakalov and Kac, "
                    + "arXiv:math/0402315v3, equation (3.13)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("third-twisted-quadratic-residue"),
                DeclarationHandle.Create(Prefix + "residue"),
                H("Native indices of a residue grid"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The set consists of integers with remainder a on division by three. "
                    + "For a = 1 or 2 the corresponding frequencies form the two complementary grids."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("third-twisted-quadratic-complementary-sums"),
                DeclarationHandle.Create(Prefix + "complementary_residue_sums"),
                H("Reflection interchanges the grid sums"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each m and polynomial Q, the sums on residues one and two agree. "
                    + "Reflection k ↦ 3m − k exchanges the grids and preserves the index-sorted pair. "
                    + "Sign ordering differs from sorting only where the fractional Heisenberg bracket vanishes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-twisted-quadratic-ordered-coefficient"),
                DeclarationHandle.Create(Prefix + "orderedCoefficient"),
                H("Coefficient of the ordered product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedProducts),
                Blocks(Paragraph(Text("The coefficient of z^(-m-2) on a polynomial Q is the sum of ordered "
                    + "pairs with first index k in residue one and second index 3m − k in residue two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("third-twisted-quadratic-finite-support"),
                DeclarationHandle.Create(Prefix + "orderedPair_finite_on_residue"),
                H("Finite support on each polynomial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each m, polynomial Q and nonzero residue a, only finitely many "
                    + "summands on that residue act nontrivially. Restrict the finite support from "
                    + "ThirdCoverComplement.complementPair_finiteSupport to the given residue. "
                    + "The normalization uses ThirdCoverComplement.inverse_scale_sq."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-twisted-quadratic-virasoro-ordered"),
                DeclarationHandle.Create(Prefix + "fractionalVirasoro_apply_ordered"),
                H("The fractional Virasoro mode as a single ordered sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On every polynomial, the complement mode equals the ordered "
                    + "coefficient plus 1/9 times the polynomial at m = 0. The two factors of the inverse "
                    + "square root account for the native one-third normalization. The native half-sum "
                    + "then splits into the two equal grid sums."))),
                DescribeRole.Theorem))));
}
