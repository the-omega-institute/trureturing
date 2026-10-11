using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Convexity;

internal sealed class LexicographicFlagRealizationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/moore1973semispaces");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A bounded orthonormal list realizes arbitrary finitely feasible strict observations.",
        H("Bounded Orthonormal Lexicographic Realization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("orthonormal-realization"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Convexity/LexicographicFlagRealization.orthonormal_realization"),
                H("A common orthonormal list"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Let V be any finite-dimensional real inner-product space and I any index type. For a family a : I → V, finite feasibility means that for every finite subset F of I there exists x in V with inner product of a(i) and x strictly positive for all i in F. No finiteness or countability condition is imposed on I.")),
                    Paragraph(Text("Write W for the real span of the range of a. If a is finitely feasible, there exist a natural number r and v : Fin r → V such that r is at most dim W, v is orthonormal, every v(k) belongs to W, and every row i has an index k with positive inner product against v(k) and zero inner products against all v(j) with j less than k. The same list works for all rows. The empty family admits the empty list.")),
                    Paragraph(Text("Projection onto W preserves every row evaluation. Compactness of its unit sphere produces a common weakly positive unit vector. The rows vanishing on that vector span a proper subspace. Recursion on this strictly smaller rank yields a residual list; prefixing the common unit vector gives an orthonormal list that settles both the positive rows and all residual rows."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("linear-form-realization"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Convexity/LexicographicFlagRealization.linear_form_realization"),
                H("Linear forms, polynomial curves, and minimum degree"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Let V be any finite-dimensional real inner-product space, I any index type, and ell : I → (V →ₗ[ℝ] ℝ) any family of algebraic linear forms. Finite dimensionality makes each form continuous; the Riesz isometry then supplies a(i) with inner product of a(i) and x equal to ell(i)(x) for every i and x. Let W be the real span of these representatives.")),
                    Paragraph(Text("The following are equivalent: every finite subset F of I admits one x with ell(i)(x) positive for all i in F; there is a natural number r and one list v : Fin r → V on which every row has a positive first nonzero entry; and there is a natural number q and v : Fin q → V such that gamma(t) = sum over j less than q of t^(j+1) times v(j) has ell(i)(gamma(t)) positive whenever 0 < t < epsilon(i), for some positive epsilon(i) depending on i.")),
                    Paragraph(Text("Under finite feasibility, the same list v can be chosen orthonormal and contained in W, with r at most dim W and dim W at most dim V. This list is lexicographically positive on all rows, its curve is eventually feasible constraintwise, and gamma(t) tends to zero as the real variable t tends to zero. If I is nonempty, r is at least one.")),
                    Paragraph(Text("There is one natural number d which is simultaneously the least attainable lexicographic list length and the least actual degree of an eventually feasible vector polynomial with zero constant coefficient. Vector polynomials use PolynomialModule ℝ V, with finite coefficient support. Their natural degree is the maximum index of a nonzero coefficient, with degree zero for the zero polynomial. This compares actual polynomial degrees even when a supplied coefficient list has trailing zero vectors.")),
                    Paragraph(Text("If I is empty, W has dimension zero, finite feasibility holds, the empty list is a lexicographic witness, its curve is identically zero, and the zero vector polynomial is feasible with degree zero. Every eventual assertion allows an individual threshold for each row; no common threshold or uniform positive margin is asserted."))),
                DescribeRole.Theorem))));
}
