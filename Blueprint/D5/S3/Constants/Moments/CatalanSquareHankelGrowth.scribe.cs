using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Moments;

internal sealed class CatalanSquareHankelGrowthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Constants/Moments/CatalanSquareHankelGrowth.";
    private static readonly LibraryNoteRef Kotesovec =
        LibraryNoteRef.Create("D5/L/Recurrence/kotesovec2016a277829a278770");
    private static readonly LibraryNoteRef Lin =
        LibraryNoteRef.Create("D5/L/Recurrence/lin2018catalanpowers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal squared-Catalan Hankel matrices are positive product Gram matrices "
            + "with explicit Chebyshev upper bounds.",
        H("Squared-Catalan Hankel Growth"),
        Blocks(
            Node("catalan-beta-measure", "The scaled beta source measure",
                "The beta distribution has parameters one half and three halves. Scaling its "
                    + "coordinate by four puts the Catalan law on the interval from zero to four. "
                    + "The proof evaluates the density integral literally; no moment identity is "
                    + "assumed as an axiom or imported theorem.",
                "catalanBetaMeasure", DescribeRole.Definition, Lin),
            Node("catalan-moment", "Literal Catalan moments",
                "The m-th moment is the integral of (4*x)^m against the beta measure. The "
                    + "proof expands the beta density, evaluates the beta and gamma factors, "
                    + "and obtains exactly Catalan(m), including m=0.",
                "catalanMoment", DescribeRole.Definition, Lin),
            Node("catalan-product-moment", "Products give squared Catalan moments",
                "Two independent copies are combined with the product measure. Product "
                    + "integration separates the powers and turns the literal product moment "
                    + "into Catalan(m)^2. This is the measure actually used by the Hankel Gram "
                    + "matrices.",
                "catalanProductMoment", DescribeRole.Definition, Lin),
            Node("catalan-square-hankel-matrix", "The exact shifted matrices",
                "At size n and shift r the Fin n matrix has entry Catalan(i+j+r)^2. Thus "
                    + "r=1 is OEIS A277829 and r=2 is A278770 after converting their one-based "
                    + "program indices to zero-based Fin indices.",
                "catalanSquareHankelMatrix", DescribeRole.Definition, Kotesovec),
            Node("catalan-square-hankel-determinant", "The determinant convention",
                "The determinant is taken over the exact shifted matrix. At n=0 this is the "
                    + "empty determinant and equals one, so the all-n positivity theorem has no "
                    + "exceptional base-case convention outside Lean.",
                "catalanSquareHankelDet", DescribeRole.Definition, Kotesovec),
            Node("positive-determinants", "Both determinant sequences are strictly positive",
                "Clipped bounded coordinates agree with the literal product coordinate on the "
                    + "support. Weighted powers are linearly independent because a polynomial "
                    + "vanishing almost everywhere on the positive open support vanishes "
                    + "identically. Transport to L2 gives positive-definite Gram matrices for "
                    + "both shifts. The entry calculation uses the literal product moment, and "
                    + "the Hadamard product of the corresponding Catalan Gram matrix with itself "
                    + "has positive determinant. This proves both positivity conjuncts for every "
                    + "n, including zero.",
                "catalan_square_hankel_det_positive", DescribeRole.Theorem, Kotesovec, Lin),
            Node("chebyshev-upper-bounds", "Monic Chebyshev-T upper bounds",
                "An affine map sends the product support [0,16] to [-1,1]. Properly scaled "
                    + "Chebyshev-T polynomials are monic and replace the power basis by a unit "
                    + "triangular change, so the Gram determinant is unchanged. Their uniform "
                    + "bound controls every changed Gram diagonal. The positive-definite "
                    + "Hadamard inequality then gives the exact factors 4^n and 16^n and the "
                    + "common factor 16^(n*(n-1)/2), without an extra n factorial.",
                "catalan_square_hankel_det_upper", DescribeRole.Theorem, Kotesovec, Lin))));

    private static DocumentBlock Node(
        string id,
        string title,
        string explanation,
        string declaration,
        DescribeRole role,
        params LibraryNoteRef[] acknowledgements) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(acknowledgements),
            Blocks(Paragraph(Text(explanation))),
            role);
}
