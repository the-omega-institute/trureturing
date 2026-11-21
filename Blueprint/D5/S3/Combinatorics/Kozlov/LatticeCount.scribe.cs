using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Kozlov;

internal sealed class LatticeCountDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Convexity/snellman2026kozlov");
    private const string Prefix = "D5/S3/Combinatorics/Kozlov/LatticeCount.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Clipping at one unit of binomial capacity separates an integral point into a residual point and a final chain member. Iterating gives the lattice transfer.",
        H("Integral decomposition and the literal lattice count"),
        Blocks(
            Node("zvector", "ZVector", "Integral f-vector coordinates", DescribeRole.Definition,
                "Use one integer coordinate for each face size from zero through n."),
            Node("intvector", "intVector", "Natural vectors as integral vectors", DescribeRole.Definition,
                "Cast the coordinates from the naturals to the integers."),
            Node("castintvector", "castIntVector", "Integral vectors as real vectors", DescribeRole.Definition,
                "Cast the integer coordinates into the real ambient space of the polytope."),
            Node("dilatelattice", "dilateLattice", "Literal lattice points in the real dilate", DescribeRole.Definition,
                "An integer vector belongs exactly when its real image lies in the scalar dilate of the convex hull of actual proper f-vectors. See Lattice/TransferEhrhart.lean, line 595."),
            Node("cast-intvector", "cast_intVector", "The two coordinate casts agree", DescribeRole.Theorem,
                "Casting a natural coordinate through the integers agrees with its direct real cast."),
            Node("natdilation", "natDilation", "Natural vectors satisfying the dilation conditions", DescribeRole.Definition,
                "Require that the coordinates cast to the reals satisfy the normalized conditions at scale r."),
            Node("dilatelattice-eq-image", "dilateLattice_eq_image", "Lattice points come from the normalized natural carrier", DescribeRole.Theorem,
                "The real dilate is nonnegative. Recover a natural vector from the nonnegative integer coordinates and use the positive dilation membership test in both directions."),
            Node("normalized-one-bounded", "normalized_one_bounded", "Rank-one lattice vectors are bounded by the capacities", DescribeRole.Theorem,
                "The first normalized coordinate equals one and antitonicity bounds every later normalized coordinate by one."),
            Node("normalized-one-fixed", "normalized_one_fixed", "Rank-one lattice vectors have the two fixed coordinates", DescribeRole.Theorem,
                "Cast back the normalized equalities in degrees zero and one."),
            Node("latticevectors", "latticeVectors", "Finite rank-one lattice carrier", DescribeRole.Definition,
                "Filter a finite box of coordinates bounded by their binomial capacities using the rank-one normalized conditions."),
            Node("mem-latticevectors", "mem_latticeVectors", "Exact membership in the finite lattice carrier", DescribeRole.Theorem,
                "The normalized conditions imply the box bounds, so filtering the box represents the entire natural rank-one lattice carrier."),
            Node("skeleton-mem-latticevectors", "skeleton_mem_latticeVectors", "Positive skeletons lie in the lattice carrier", DescribeRole.Theorem,
                "The skeleton is integral and is a proper f-vector, hence lies in the rank-one convex hull."),
            Node("lattice-terminal", "lattice_terminal", "The terminal rank-one lattice vector is full", DescribeRole.Theorem,
                "If the top coordinate is positive it reaches its unit capacity. Monotonicity of normalized coordinates forces every earlier coordinate to reach capacity too."),
            Node("lattice-chained-exists", "lattice_chained_exists", "Chained integral decomposition for every positive rank", DescribeRole.Theorem,
                "This is the equal-shift Kozlov case of Part III, Theorem 6 and Corollary 7. Clip the vector at the rank-one capacities and subtract this last member. The residual ratios are the positive parts after subtracting one, so they are antitone. A deficient coordinate of the clipped member forces the residual to vanish from that degree onward. Induct on rank and append the clipped member."),
            Node("lattice-count-transfer", "lattice_count_transfer", "The transfer formula for literal lattice points", DescribeRole.Theorem,
                "The natural-dilation carrier is the image of chained rank-one lattice tuples. Use the integral decomposition for surjectivity, uniqueness of bounded chained sums, and the injective coordinate cast. See Part III, Corollary 33 and Lattice/TransferEhrhart.lean, line 613."))));

    private static DocumentBlock Node(string id, string name, string title, DescribeRole role, string prose, Formula? formula = null) =>
        Describe.Lean(DescribeId.Create("kozlov-lattice-count-" + id),
            DeclarationHandle.Create(Prefix + name), H(title),
            formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            name is "dilateLattice" or "lattice_chained_exists" or "lattice_count_transfer"
                ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
