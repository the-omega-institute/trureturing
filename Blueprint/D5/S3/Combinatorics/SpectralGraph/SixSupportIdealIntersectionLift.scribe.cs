using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class SixSupportIdealIntersectionLiftDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/SixSupportIdealIntersectionLift.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create(
        "D5/L/GraphInvariants/idealintersection2026sixsupport");

    private static DocumentBlock Item(string id, string declaration, string title,
        string text, DescribeRole role) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
        Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact six-cell quotient acts on every actual three-prime ideal-intersection graph.",
        H("From the quotient eigenvector to actual ideals"),
        Blocks(
            Item("ordered-exponent-vector", "exponents", "The three exponents",
                "The exponent vector is exactly (a,b,c) on Fin 3. Positive integer "
                + "parameters count ideals; real positive parameters in the spectral "
                + "supplier do not independently define ideal multiplicities.",
                DescribeRole.Definition),
            Item("six-support-cells", "cell", "All active cells in source order",
                "The six cells are {0},{1},{2},{0,1},{0,2},{1,2}, corresponding to "
                + "the source order 1,2,3,12,13,23. Empty and full support are treated "
                + "separately. A prime injection binds these coordinates to three "
                + "distinct primes without changing their values.", DescribeRole.Definition),
            Item("extend-by-zero", "value", "The exact support-vector extension",
                "A quotient vector z has value z_i on cell i and zero on empty "
                + "and full support. No assertion of an operator identity at the "
                + "empty nonvertex is used. Its lift is constant on each actual "
                + "exponent-box support fiber.", DescribeRole.Definition),
            Item("actual-six-cell-lift", "actual_eigenvalue", "Reflect every nonzero quotient eigenvalue",
                "For any three distinct primes and positive integers a,b,c, let "
                + "C be the literal SixSupportLaplacianLowRoot quotient. A nonzero "
                + "vector z with C*z=e*z and e nonzero produces a nonzero actual "
                + "ideal-graph eigenvector with eigenvalue V-e, where "
                + "V=(a+1)(b+1)(c+1)-2. The support action is computed on every "
                + "nonempty support. The existing weighted left-null identity "
                + "forces weighted sum zero because e is nonzero. The exact fiber "
                + "sum then gives zero sum on the exponent box. Positive fiber "
                + "weights and a nonzero coordinate give a nonzero lift. Finally "
                + "IdealIntersectionObstructions.actual_eigenvalue_of_support "
                + "transports it through the existing actual ideal/support graph "
                + "isomorphism. Zero sum and nonvacuity are derived, not assumed "
                + "as a replacement for this correspondence.", DescribeRole.Theorem),
            Item("actual-low-root-application", "result", "The positive-real supplier has a graph consumer",
                "For all ordered positive integer triples a<=b<=c and every three "
                + "distinct primes, the actual ideal-intersection Laplacian has "
                + "an eigenvalue strictly between V-3 and V. This consumes the "
                + "existing full positive-real low-eigenvalue theorem, including "
                + "its nonzero eigenvector. It is not by itself a proof of "
                + "nonintegrality: V-2 and V-1 are still possible integers in the "
                + "interval. The full repeated/small-minimum/endpoint/largest-root "
                + "classification and its 325, 27562 and 8658 finite foundations "
                + "remain separate obligations. Neither this three-prime lift "
                + "nor the earlier paired four-prime lift solves general Q3.",
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot")),
         DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions"))]));
}
