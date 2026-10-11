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
                DescribeRole.Theorem))));
}
